<?xml version="1.0" standalone="no"?>

<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
                
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
	
	
<!-- 
		 ===========================================================
			Handle Bucket connections to the shared busses.
		 ===========================================================
-->		
	
<xsl:template name="BCLaneSpace_BucketToSharedBus">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="sbs_idx_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE= $busName)]/@BUSINDEX"/>
	<xsl:variable name="sbs_name_" select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@BUSINDEX = $sbs_idx_)]/@BUSNAME"/>
					
	<xsl:variable name="sbs_bc_y_" select="($sbs_Y + ($sbs_idx_ * $SBS_LANE_H))"/>
					
	<xsl:variable name="bktshp_hori_idx_" select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@BUSINDEX = $sbs_idx_)]/@STACK_HORIZ_INDEX"/>
	<xsl:variable name="bktshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@BUSINDEX = $sbs_idx_)]/@SHAPE_VERTI_INDEX"/>
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>
	
	<xsl:variable name="bktshp_Y_">
		<xsl:call-template name="_calc_Stack_Shape_Y">
			<xsl:with-param name="horizIdx"  select="$bktshp_hori_idx_"/>
			<xsl:with-param name="vertiIdx"  select="$bktshp_vert_idx_"/>
		</xsl:call-template>
	</xsl:variable>
						
	<xsl:variable name="sbsStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
				
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
				<xsl:if test="($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_)">
					<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
				</xsl:if>	
				
				<xsl:if test="not($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_)">0</xsl:if>	
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="vert_line_x_"  select="($laneInSpace_X  +  ceiling($BIFC_W div 2))"/>
	<xsl:variable name="vert_line_y1_" select="($sbs_Y     + ($sbs_idx_ * $SBS_LANE_H) + ceiling($BIFC_W div 2))"/>
	<xsl:variable name="vert_line_y2_" select="($bktshp_Y_ + ceiling($periMOD_W div 2) + $sbsStack_H_diff_)"/>
	<xsl:variable name="bcInSpace_X_"  select="($laneInSpace_X  +  ceiling($BIFC_W div 2) - ceiling($BUS_ARROW_W div 2))"/>
	
	<xsl:variable name="horz_line_y_"   select="$vert_line_y2_"/>
	<xsl:variable name="horz_line_x1_"  select="$vert_line_x_"/>
	<xsl:variable name="horz_line_x2_" select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_)"/>
	
	<xsl:variable name="v_bus_ul_x_"   select="$vert_line_x_"/>
	<xsl:variable name="v_bus_ul_y_"   select="$vert_line_y1_"/>
	<xsl:variable name="v_bus_width_"  select="$P2P_BUS_W"/>
	<xsl:variable name="v_bus_height_" select="($vert_line_y2_ - $vert_line_y1_ - ceiling($BIFC_H div 2))"/>
	
	<xsl:variable name="h_bus_ul_x_"   select="$v_bus_ul_x_"/>
	<xsl:variable name="h_bus_ul_y_"   select="$vert_line_y2_   - $BIFC_H + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
	<xsl:variable name="h_bus_width_"  select="($space_W_ + ceiling(($extSpaceWest_W_ + $extSpaceEast_W_) div 2) - $BIFC_W)"/>
	<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
	
<!--	
	<xsl:message>v bus x <xsl:value-of select="$v_bus_ul_x_"/></xsl:message>
	<xsl:message>v bus y <xsl:value-of select="$v_bus_ul_y_"/></xsl:message>
	<xsl:message>v bus w <xsl:value-of select="$v_bus_width_"/></xsl:message>
	<xsl:message>v bus h <xsl:value-of select="$v_bus_height_"/></xsl:message>
-->	
	
	<!-- Draw rectangular parts of the bus -->
	<rect x="{$v_bus_ul_x_}" 
	  	  y="{$v_bus_ul_y_ - 2}"  
	 	  width= "{$v_bus_width_}" 
	 	  height="{$v_bus_height_}" 
	 	  style="stroke:none; fill:{$bus_color_}"/>
		
	
	<rect x="{$h_bus_ul_x_}" 
	  	  y="{$h_bus_ul_y_ - 5}"  
	 	  width= "{$h_bus_width_}" 
	 	  height="{$h_bus_height_}" 
	 	  style="stroke:none; fill:{$bus_color_}"/>
		
	
</xsl:template>					
	
	
	
<!--
		 ===========================================================
			Handle Processor's Shared bus connections.
		 ===========================================================
-->
	
<xsl:template name="BCLaneSpace_ProcBifToSharedBus">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
<!--						
	
						<xsl:message>Proc diff  <xsl:value-of select="$procStack_H_diff_"/></xsl:message>
						<xsl:message>Proc inst  <xsl:value-of select="$procInst_"/></xsl:message>
						<xsl:message>Proc Bif Name <xsl:value-of select="$procBifName_"/></xsl:message>
						<xsl:message>Proc Bif Rank <xsl:value-of select="$procBifRank_"/></xsl:message>
-->
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="sbs_idx_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE= $busName)]/@BUSINDEX"/>
	<xsl:variable name="sbs_bc_y_" select="($sbs_Y + ($sbs_idx_ * $SBS_LANE_H))"/>
						
	<xsl:variable name="procInst_" select="BUSCONN/@INSTANCE"/>
	
<!--	
	<xsl:message>Proc inst  <xsl:value-of select="$procInst_"/></xsl:message>
-->						
	
	<xsl:variable name="procBif_Y_"    select="((($BIF_H + $MOD_BIF_GAP_V) * BUSCONN/@BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
	<xsl:variable name="procBifName_"  select="BUSCONN/@BUSINTERFACE"/>
	<xsl:variable name="procBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInst_)]/BUSINTERFACE[(@NAME = $procBifName_)]/@BIF_X"/>
	<xsl:variable name="procBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInst_)]/BUSINTERFACE[(@NAME = $procBifName_)]/@BIFRANK"/>
						
	<xsl:variable name="procshp_hori_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInst_)]/@STACK_HORIZ_INDEX"/>
	<xsl:variable name="procshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInst_)]/@SHAPE_VERTI_INDEX"/>
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>
	
						
<!--						
	<xsl:message>Stack horiz  <xsl:value-of select="$procshp_hori_idx_"/></xsl:message>
	<xsl:message>Stack verti  <xsl:value-of select="$procshp_vert_idx_"/></xsl:message>
	<xsl:message>Proc Bif Y   <xsl:value-of select="$procBif_Y_"/></xsl:message>
-->						
						
	<xsl:variable name="procshp_Y_">
		<xsl:call-template name="_calc_Stack_Shape_Y">
			<xsl:with-param name="horizIdx"  select="$procshp_hori_idx_"/>
			<xsl:with-param name="vertiIdx"  select="$procshp_vert_idx_"/>
		</xsl:call-template>
	</xsl:variable>
						
	
	<xsl:variable name="procStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
		
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
				<xsl:choose>
					<xsl:when test="(($procshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
						<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:when test="(($procshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
						<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:otherwise>0</xsl:otherwise>	
				</xsl:choose>	
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="bc_Y_"  select="($procshp_Y_ + $procBif_Y_ + ceiling($BIF_H div 2) + $procStack_H_diff_) - ceiling($BIFC_H div 2)"/>
<!--	
	<xsl:variable name="bc_x_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2))"/>
	<xsl:variable name="bc_x_"  select="0"/>
-->	
	<xsl:variable name="bc_X_">
		<xsl:choose>
			<xsl:when test="$procBifSide_ = '0'">
		 		<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($periMOD_W div 2) + $BIFC_W))"/>
<!--				
		 		<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - ceiling($periMOD_W div 2))"/>
		 		<xsl:value-of select="($space_W_ -  ceiling($periMOD_W div 2))"/>
-->				
			</xsl:when>
			<xsl:when test="$procBifSide_ = '1'">
		 		<xsl:value-of select="ceiling($periMOD_W div 2)"/>
			</xsl:when>
			<xsl:otherwise>0</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
						
	<!-- Place the bus connection -->
	<use   x="{$bc_X_}"   y="{$bc_Y_}"  xlink:href="#{$busStd}_busconn_{$procBifRank_}"/>
						
	
<!--	
	<use   x="{$laneInSpace_X}"   y="{$sbs_bc_y_ - ceiling($BIFC_H div 4)}"  xlink:href="#{$busStd}_busconn_{$procBifRank_}"/>
-->	
	
						
	<xsl:variable name="vert_line_x_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2))"/>
	<xsl:variable name="vert_line_y1_" select="($procshp_Y_ + $procBif_Y_ + ceiling($BIF_H div 2) + $procStack_H_diff_)"/>
	<xsl:variable name="vert_line_y2_"  select="($sbs_Y    + ($sbs_idx_ * $SBS_LANE_H) + ceiling($BIFC_W div 2))"/>			
		
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
	
	<xsl:variable name="v_bus_ul_x_">
		<xsl:choose>
			<xsl:when test="@ORIENTED='WEST'">
				<xsl:value-of select="($vert_line_x_ + $MOD_BIF_GAP_H)"/>
			</xsl:when>
			<xsl:when test="@ORIENTED='EAST'">
				<xsl:value-of select="($vert_line_x_ - $MOD_BIF_GAP_H)"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
		
		
	<xsl:variable name="v_bus_width_" select="$P2P_BUS_W"/>
	<xsl:variable name="v_bus_height_">
		<xsl:choose>
			<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
				<xsl:value-of select="($vert_line_y1_ - $vert_line_y2_) - $P2P_BUS_W"/>
			</xsl:when>
			<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
				<xsl:value-of select="($vert_line_y2_ - $vert_line_y1_) - $P2P_BUS_W"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
		
	<xsl:variable name="h_bus_ul_x_">
		<xsl:choose>
			<xsl:when test="@ORIENTED='WEST'">
				<xsl:value-of select="($bc_X_ + $BIFC_W - ceiling(($BIFC_W - $BIFC_Wi) div 2))"/>
<!--				
				<xsl:value-of select="$v_bus_ul_x_"/>
-->	
			</xsl:when>
			<xsl:when test="@ORIENTED='EAST'">
				<xsl:value-of select="$v_bus_ul_x_"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
		
		<xsl:variable name="h_bus_ul_y_">
			<xsl:choose>
				<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
					<xsl:value-of select="$vert_line_y2_ - ceiling($P2P_BUS_W div 2)"/>
				</xsl:when>
				<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
					<xsl:value-of select="$vert_line_y1_ - ceiling($P2P_BUS_W div 2)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
	
	
		<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
		<xsl:variable name="h_bus_width_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="$v_bus_ul_x_ - $h_bus_ul_x_ + $P2P_BUS_W"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($bc_X_ - $v_bus_ul_x_) + ceiling(($BIFC_W - $BIFC_Wi) div 2) + 1"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
	
	
			
<!--			
		<xsl:if test="(@ORIENTED = 'WEST')">
		</xsl:if>
			
 		<xsl:message>bc_X_  <xsl:value-of select="$bc_X_"/></xsl:message>
 		<xsl:message>v_bus_ul_x  <xsl:value-of select="$v_bus_ul_x_"/></xsl:message>
 		<xsl:message>h_bus_width <xsl:value-of select="$h_bus_width_"/></xsl:message>
 		<xsl:message>h_bus_ul_y  <xsl:value-of select="$h_bus_ul_y_"/></xsl:message>
-->	
			
		<rect x="{$v_bus_ul_x_}" 
		  	  y="{$v_bus_ul_y_ + 2}"  
		 	  width= "{$v_bus_width_}" 
		 	  height="{$v_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_color_}"/>
		
		<rect x="{$h_bus_ul_x_}" 
		  	  y="{$h_bus_ul_y_}"  
		 	  width= "{$h_bus_width_}" 
		 	  height="{$h_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_color_}"/>
		
<!--						
		<xsl:message>Proc diff  <xsl:value-of select="$procStack_H_diff_"/></xsl:message>
		<xsl:message>Proc inst  <xsl:value-of select="$procInst_"/></xsl:message>
		<xsl:message>Proc Bif Name <xsl:value-of select="$procBifName_"/></xsl:message>
		<xsl:message>Proc Bif Rank <xsl:value-of select="$procBifRank_"/></xsl:message>
-->
	
</xsl:template>					
	
					
<!--
		 ===========================================================
			Handle non Processor Sharedebus connections.
		 ===========================================================
-->
				
<xsl:template name="BCLaneSpace_NonProcBifToSharedBus">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
						
	<xsl:variable name="sbs_idx_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE= $busName)]/@BUSINDEX"/>
	<xsl:variable name="sbs_bc_y_" select="($sbs_Y + ($sbs_idx_ * $SBS_LANE_H))"/>
						
	<xsl:variable name="cmplxInst_" select="BUSCONN/@INSTANCE"/>
						
	<xsl:variable name="cmplxBif_Y_"    select="((($BIF_H + $MOD_BIF_GAP_V) * BUSCONN/@BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
	<xsl:variable name="cmplxBifName_"  select="BUSCONN/@BUSINTERFACE"/>
	<xsl:variable name="cmplxBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $cmplxInst_)]/BUSINTERFACE[(@NAME = $cmplxBifName_)]/@BIF_X"/>
	<xsl:variable name="cmplxBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $cmplxInst_)]/BUSINTERFACE[(@NAME = $cmplxBifName_)]/@BIFRANK"/>
						
	<xsl:variable name="cmplxshp_hori_idx_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $cmplxInst_)])]/@STACK_HORIZ_INDEX"/>
	<xsl:variable name="cmplxshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $cmplxInst_)])]/@SHAPE_VERTI_INDEX"/>
						
	<xsl:variable name="is_abvSbs_" select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $cmplxInst_)]]/@IS_ABVSBS)"/>
	<xsl:variable name="is_blwSbs_" select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $cmplxInst_)]]/@IS_BLWSBS)"/>
	
<!--						
	<xsl:message><xsl:value-of select="$cmplxInst_"/> : <xsl:value-of select="$is_blwSbs_"/></xsl:message>
	<xsl:message><xsl:value-of select="$cmplxInst_"/> : <xsl:value-of select="$is_abvSbs_"/></xsl:message>
	<xsl:message>Stack horiz  <xsl:value-of select="$cmplxshp_hori_idx_"/></xsl:message>
	<xsl:message>Stack verti  <xsl:value-of select="$cmplxshp_vert_idx_"/></xsl:message>
	<xsl:message>Proc Bif Y   <xsl:value-of select="$procBif_Y_"/></xsl:message>
-->						
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>						
	
	<xsl:variable name="cmplxshp_Y_">
		<xsl:call-template name="_calc_Stack_Shape_Y">
			<xsl:with-param name="horizIdx"  select="$cmplxshp_hori_idx_"/>
			<xsl:with-param name="vertiIdx"  select="$cmplxshp_vert_idx_"/>
		</xsl:call-template>
	</xsl:variable>
						
	<xsl:variable name="cmplxStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
				
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
				<xsl:choose>
						<xsl:when test="(($cmplxshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
							<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
						</xsl:when>	
						<xsl:when test="(($cmplxshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
							<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
						</xsl:when>	
						<xsl:otherwise>0</xsl:otherwise>	
				</xsl:choose>	
									
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="bc_Y_"  select="($cmplxshp_Y_ + $cmplxBif_Y_ + ceiling($BIF_H div 2) + $cmplxStack_H_diff_) - ceiling($BIFC_H div 2)"/>
	
<!--	
	<xsl:variable name="bc_x_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2))"/>
	<xsl:variable name="bc_x_"  select="0"/>
-->	
	<xsl:variable name="bc_X_">
		<xsl:choose>
			<xsl:when test="$cmplxBifSide_ = '0'">
		 		<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($periMOD_W div 2) + $BIFC_W))"/>
			</xsl:when>
			<xsl:when test="$cmplxBifSide_ = '1'">
		 		<xsl:value-of select="ceiling($periMOD_W div 2)"/>
			</xsl:when>
			<xsl:otherwise>0</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>	
	
	<use   x="{$bc_X_}"   y="{$bc_Y_}"  xlink:href="#{$busStd}_busconn_{$cmplxBifRank_}"/>
	
<!--	
	<xsl:message>Bif Rank <xsl:value-of select="$cmplxBifRank_"/></xsl:message>
-->	
	<xsl:variable name="vert_line_x_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2))"/>
	<xsl:variable name="vert_line_y1_" select="($cmplxshp_Y_ + $cmplxBif_Y_ + ceiling($BIF_H div 2) + $cmplxStack_H_diff_)"/>
	<xsl:variable name="vert_line_y2_"  select="($sbs_Y    + ($sbs_idx_ * $SBS_LANE_H) + ceiling($BIFC_W div 2))"/>
	
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
	
	<xsl:variable name="v_bus_ul_x_">
		<xsl:choose>
			<xsl:when test="@ORIENTED='WEST'">
				<xsl:value-of select="($vert_line_x_ + $MOD_BIF_GAP_H)"/>
			</xsl:when>
			<xsl:when test="@ORIENTED='EAST'">
				<xsl:value-of select="($vert_line_x_ - $MOD_BIF_GAP_H)"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
		
	<xsl:variable name="v_bus_width_" select="$P2P_BUS_W"/>
	<xsl:variable name="v_bus_height_">
		<xsl:choose>
			<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
				<xsl:value-of select="($vert_line_y1_ - $vert_line_y2_) - $P2P_BUS_W + 8"/>
			</xsl:when>
			<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
				<xsl:value-of select="($vert_line_y2_ - $vert_line_y1_) - $P2P_BUS_W + 8"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
		
	<xsl:variable name="h_bus_ul_x_">
		<xsl:choose>
			<xsl:when test="@ORIENTED='WEST'">
				<xsl:value-of select="($bc_X_ + $BIFC_W - ceiling(($BIFC_W - $BIFC_Wi) div 2))"/>
			</xsl:when>
			<xsl:when test="@ORIENTED='EAST'">
				<xsl:value-of select="$v_bus_ul_x_"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
		
	<xsl:variable name="h_bus_ul_y_">
		<xsl:choose>
			
			<xsl:when test="($is_blwSbs_ = 'TRUE') and ($vert_line_y1_ &gt; $vert_line_y2_)">
				<xsl:value-of select="$vert_line_y1_ - ceiling($P2P_BUS_W div 2)"/>
			</xsl:when>
			<xsl:when test="($is_blwSbs_ = 'TRUE') and ($vert_line_y2_ &gt; $vert_line_y1_)">
				<xsl:value-of select="$vert_line_y2_ - ceiling($P2P_BUS_W div 2)"/>
			</xsl:when>
			
			<xsl:when test="($is_abvSbs_ = 'TRUE') and ($vert_line_y1_ &gt; $vert_line_y2_)">
				<xsl:value-of select="$vert_line_y2_ - ceiling($P2P_BUS_W div 2)"/>
			</xsl:when>
			<xsl:when test="($is_abvSbs_ = 'TRUE') and ($vert_line_y2_ &gt; $vert_line_y1_)">
				<xsl:value-of select="$vert_line_y1_ - ceiling($P2P_BUS_W div 2)"/>
			</xsl:when>
			
		</xsl:choose>
	</xsl:variable>	
	
	
	<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
	<xsl:variable name="h_bus_width_">
		<xsl:choose>
			<xsl:when test="@ORIENTED='WEST'">
				<xsl:value-of select="$v_bus_ul_x_ - $h_bus_ul_x_ + $P2P_BUS_W"/>
			</xsl:when>
			<xsl:when test="@ORIENTED='EAST'">
				<xsl:value-of select="($bc_X_ - $v_bus_ul_x_) + ceiling(($BIFC_W - $BIFC_Wi) div 2) + 1"/>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>	
	
			
		<rect x="{$v_bus_ul_x_}" 
		  	  y="{$v_bus_ul_y_ - 2}"  
		 	  width= "{$v_bus_width_}" 
		 	  height="{$v_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_color_}"/>
		
		<rect x="{$h_bus_ul_x_}" 
		  	  y="{$h_bus_ul_y_}"  
		 	  width= "{$h_bus_width_}" 
		 	  height="{$h_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_color_}"/>
		
</xsl:template>					
	
<!-- 
		 ===========================================================
			Handle connections from processors to Memory UNITs
		 ===========================================================
-->
	
<xsl:template name="BCLaneSpace_ProcBifToMemoryUnit">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
						
	
<!--	
	<xsl:variable name="bcInSpace_X_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2) - ceiling($BUS_ARROW_W div 2))"/>
-->
	<xsl:variable name="bcInSpace_X_"  select="$laneInSpace_X"/>
	<xsl:variable name="procInstance_" select="BUSCONN[@IS_PROCONN]/@INSTANCE"/>
	<xsl:variable name="mem_procshp_hori_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInstance_)]/@STACK_HORIZ_INDEX"/>
	<xsl:variable name="mem_procshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInstance_)]/@SHAPE_VERTI_INDEX"/>
						
	<xsl:variable name="mem_procshp_Y_">
		<xsl:call-template name="_calc_Stack_Shape_Y">
			<xsl:with-param name="horizIdx"  select="$mem_procshp_hori_idx_"/>
			<xsl:with-param name="vertiIdx"  select="$mem_procshp_vert_idx_"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>							
	
	<xsl:variable name="cmplxStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
				
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
				<xsl:choose>
					<xsl:when test="(($mem_procshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
						<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:when test="(($mem_procshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
						<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:otherwise>0</xsl:otherwise>	
				</xsl:choose>	
									
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
						
	<xsl:variable name="mem_procStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
	
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
			<xsl:choose>
				<xsl:when test="(($mem_procshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
					<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
				</xsl:when>	
				<xsl:when test="(($mem_procshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
					<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
				</xsl:when>	
				<xsl:otherwise>0</xsl:otherwise>	
			</xsl:choose>	
									
		</xsl:when>
	</xsl:choose>
  </xsl:variable>
						
	<!-- Store the conns in a variable -->	
	<xsl:variable name="memConn_heights_">

		<xsl:for-each select="BUSCONN">
								
			<xsl:variable name="bifName_"       select="@BUSINTERFACE"/>
			
							
			<xsl:choose>
				<xsl:when test="@IS_PROCONN and @BIF_Y">
							
					<xsl:variable name="procBif_Y_"    select="((($BIF_H + $MOD_BIF_GAP_V) * @BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
					<xsl:variable name="procBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
					<xsl:variable name="procBusName_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BUSNAME"/>
					<xsl:variable name="procBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
					<xsl:variable name="bcProc_Y_"     select="($mem_procshp_Y_ + $procBif_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $mem_procStack_H_diff_)"/>
					<xsl:variable name="bcProc_X_">
						<xsl:choose>
							<xsl:when test="$procBifSide_ = '0'">
		 						<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($periMOD_W div 2) + $BIFC_W))"/>
							</xsl:when>
							<xsl:when test="$procBifSide_ = '1'">
		 						<xsl:value-of select="ceiling($periMOD_W div 2)"/>
							</xsl:when>
							<xsl:otherwise>0</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
						
					<MEMCONN X="{$bcProc_X_}" Y="{$bcProc_Y_}" BUSNAME="{$procBusName_}" BUSSTD="{$busStd}" BIFRANK="{$procBifRank_}" BIFSIDE="{$procBifSide_}"/>
										
				</xsl:when>
									
				<xsl:otherwise>
									
					<xsl:variable name="memcInstance_"  select="@INSTANCE"/>
					<xsl:variable name="memcshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $memcInstance_)]]/@SHAPE_VERTI_INDEX"/>
					<xsl:variable name="memcBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $memcInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
					<xsl:variable name="memcBif_Y_"    select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $memcInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_Y"/>
										
					<xsl:variable name="memshp_Y_">
						<xsl:call-template name="_calc_Stack_Shape_Y">
							<xsl:with-param name="horizIdx"  select="$mem_procshp_hori_idx_"/>
							<xsl:with-param name="vertiIdx"  select="$memcshp_vert_idx_"/>
						</xsl:call-template>
				    </xsl:variable>
					
					<xsl:variable name="memcMOD_W_" select="((/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $memcInstance_)]]/@MODS_W) * $periMOD_W)"/>
										
					<xsl:variable name="procBif_Y_"   select="((($BIF_H + $MOD_BIF_GAP_V) * @BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
					
					<xsl:variable name="memcConn_Y_">
						<xsl:choose>
							<xsl:when test="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $memcInstance_)]]/@MODS_H = 1)">
								<xsl:value-of  select="($memshp_Y_ + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V) +  ($memcBif_Y_ * ($BIF_H + $MOD_BIF_GAP_V)) + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $cmplxStack_H_diff_)"/>
							</xsl:when>
							<xsl:otherwise>
								<xsl:value-of  select="($memshp_Y_ + $periMOD_H + $MOD_LANE_H + ($memcBif_Y_ * ($BIF_H + $MOD_BIF_GAP_V)) + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2))"/>
							</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
					
					<xsl:variable name="memcConn_X_">
						<xsl:choose>
							<xsl:when test="$memcBifSide_ = '0'">
 								<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($memcMOD_W_ div 2) + $BIFC_W))"/>
							</xsl:when>
							<xsl:when test="$memcBifSide_ = '1'">
 								<xsl:value-of select="ceiling($memcMOD_W_ div 2)"/>
							</xsl:when>
						</xsl:choose>
					</xsl:variable>
						
					<xsl:variable name="memcBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $memcInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
					<xsl:variable name="memcBusName_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $memcInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BUSNAME"/>
					
					<MEMCONN X="{$memcConn_X_}" Y="{$memcConn_Y_}" BUSNAME="{$memcBusName_}" BUSSTD="{$busStd}" BIFRANK="{$memcBifRank_}" BIFSIDE="{$memcBifSide_}"/>
					
				</xsl:otherwise>
			</xsl:choose>
		</xsl:for-each>
	</xsl:variable>
						
						
	<!-- Draw the busconnection and horizontal lines.-->						
	<xsl:for-each select="exsl:node-set($memConn_heights_)/MEMCONN">
							
		<xsl:variable name="bus_x_" select="($bcInSpace_X_ + ceiling($BIFC_W div 2))"/>
		<xsl:variable name="bus_y_" select="@Y + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
		
		<xsl:variable name="h_bus_ul_x_">
			<xsl:choose>
				<xsl:when test="@BIFSIDE='0'">
					<xsl:value-of select="$bus_x_"/>
				</xsl:when>
				<xsl:when test="@BIFSIDE='1'">
					<xsl:value-of select="(@X + $BIFC_W + $BUS_ARROW_W)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<xsl:variable name="h_bus_ul_y_" select="$bus_y_"/>
	
		<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
		<xsl:variable name="h_bus_width_">
			<xsl:choose>
				<xsl:when test="@BIFSIDE='0'">
					<xsl:value-of select="(@X - $bus_x_ - $BUS_ARROW_W)"/>
				</xsl:when>
				<xsl:when test="@BIFSIDE='1'">
					<xsl:value-of select="$bus_x_ - $h_bus_ul_x_"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
<!--		
 		<xsl:message>bc_X_       <xsl:value-of select="@X"/></xsl:message>
 		<xsl:message>h_bus_ul_x  <xsl:value-of select="$h_bus_ul_x_"/></xsl:message>
 		<xsl:message>h_bus_ul_y  <xsl:value-of select="$h_bus_ul_y_"/></xsl:message>
 		<xsl:message>h_bus_width <xsl:value-of select="$h_bus_width_"/></xsl:message>
-->		
		
		<!-- Place the bus connection -->
		<use   x="{@X}"   y="{@Y}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
		
		<!-- Draw the arrow -->
		<xsl:choose>
			<xsl:when test="@BIFSIDE='0'">
				<use   x="{@X - $BUS_ARROW_W}"   y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowEast"/>
			</xsl:when>
			<xsl:when test="@BIFSIDE='1'">
				<use   x="{(@X + $BIFC_W)}" y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowWest"/>
			</xsl:when>
		</xsl:choose>
		
		
		<!-- Draw the horizontal part of the bus -->
		<rect x="{$h_bus_ul_x_}" 
		  	  y="{$h_bus_ul_y_}"  
		 	  width= "{$h_bus_width_}" 
		 	  height="{$h_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_color_}"/>
		
	</xsl:for-each>
						
	<xsl:variable name="busTop_"  select="math:min(exsl:node-set($memConn_heights_)/MEMCONN/@Y)"/>
	<xsl:variable name="busBot_"  select="math:max(exsl:node-set($memConn_heights_)/MEMCONN/@Y)"/>
	<xsl:variable name="busName_" select="exsl:node-set($memConn_heights_)/MEMCONN/@BUSNAME"/>
	
	<xsl:variable name="v_bus_y_" select="$busTop_ + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
	
	
	<!-- Draw the vertical part of the bus -->	
	<rect x="{$bcInSpace_X_ + $P2P_BUS_W}" 
	  	  y="{$v_bus_y_}"  
	 	  width= "{$P2P_BUS_W}" 
	 	  height="{($busBot_ - $busTop_) + $P2P_BUS_W}" 
	 	  style="stroke:none; fill:{$bus_color_}"/>
	
	<!-- Place the bus label.-->	
	<text class="p2pbuslabel" 
			  x="{$bcInSpace_X_   + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 6}"
			  y="{$busTop_ + ($BUS_ARROW_H * 3)}">
			<xsl:value-of select="$busName_"/>
	</text>	
	
						
</xsl:template>					
	
	
<!-- 
		 ===========================================================
			Handle generic Point to Point connections
		 ===========================================================
-->
	
<xsl:template name="BCLaneSpace_PointToPoint">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	<xsl:variable name="bus_color_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>							
	
	<xsl:variable name="bcInSpace_X_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2) - ceiling($BUS_ARROW_W div 2))"/>
	<xsl:variable name="p2pInstance_" select="BUSCONN[(@BIF_Y)]/@INSTANCE"/>
					
	<xsl:variable name="p2pshp_hori_idx_">
		<xsl:choose>
			<xsl:when test="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $p2pInstance_)]">
				<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $p2pInstance_)]/@STACK_HORIZ_INDEX"/>
			</xsl:when>
			<xsl:otherwise>
				<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $p2pInstance_)])]/@STACK_HORIZ_INDEX"/>
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>		
					
	<xsl:variable name="p2pshp_vert_idx_">
		<xsl:choose>
			<xsl:when test="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $p2pInstance_)]">
				<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $p2pInstance_)]/@SHAPE_VERTI_INDEX"/>
			</xsl:when>
			<xsl:otherwise>
				<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $p2pInstance_)])]/@SHAPE_VERTI_INDEX"/>
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>		
					
<!--					
					<xsl:variable name="p2pshp_hori_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInstance_)]/@STACK_HORIZ_INDEX"/>
					<xsl:variable name="p2pshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInstance_)]/@SHAPE_VERTI_INDEX"/>
-->					
						
	<xsl:variable name="p2pshp_Y_">
		<xsl:call-template name="_calc_Stack_Shape_Y">
			<xsl:with-param name="horizIdx"  select="$p2pshp_hori_idx_"/>
			<xsl:with-param name="vertiIdx"  select="$p2pshp_vert_idx_"/>
		</xsl:call-template>
	</xsl:variable>
			
	<xsl:variable name="cmplxStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
				
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
				<xsl:choose>
					<xsl:when test="(($p2pshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
						<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:when test="(($p2pshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
						<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:otherwise>0</xsl:otherwise>	
				</xsl:choose>	
									
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
						
																				
	<xsl:variable name="procStack_H_diff_">
		<xsl:choose>
			<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
			
				<xsl:variable name="stackToWest_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToWest"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="stackToEast_AbvSbs_H_">
					<xsl:call-template name="_calc_Stack_AbvSbs_Height">
						<xsl:with-param name="stackIdx"  select="$stkToEast"/>
					</xsl:call-template>
				</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
				<xsl:choose>
					<xsl:when test="(($p2pshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
						<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:when test="(($p2pshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
						<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
					</xsl:when>	
					<xsl:otherwise>0</xsl:otherwise>	
				</xsl:choose>	
									
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
						
	
	
	<!-- Store the conns in a variable -->	
	<xsl:variable name="p2pConn_heights_">
	
		<xsl:for-each select="BUSCONN">
									
			<xsl:variable name="bifName_" select="@BUSINTERFACE"/>
							
				<xsl:choose>
					<xsl:when test="@IS_PROCONN and @BIF_Y">
										
<!--										
										<xsl:message>Proc <xsl:value-of select="$procInstance_"/></xsl:message>
-->										
						<xsl:variable name="procBif_Y_"   select="((($BIF_H + $MOD_BIF_GAP_V) * @BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
						<xsl:variable name="procBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $p2pInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
						<xsl:variable name="procBusName_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $p2pInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BUSNAME"/>
						<xsl:variable name="procBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $p2pInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
										
						<xsl:variable name="bcProc_Y_"     select="($p2pshp_Y_ + $procBif_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $procStack_H_diff_)"/>
						<xsl:variable name="bcProc_X_">
							<xsl:choose>
								<xsl:when test="$procBifSide_ = '0'">
		 							<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($periMOD_W div 2) + $BIFC_W))"/>
								</xsl:when>
								<xsl:when test="$procBifSide_ = '1'">
		 							<xsl:value-of select="ceiling($periMOD_W div 2)"/>
								</xsl:when>
								<xsl:otherwise>0</xsl:otherwise>
							</xsl:choose>
						</xsl:variable>
						
						<P2PCONN X="{$bcProc_X_}" Y="{$bcProc_Y_}" BUSNAME= "{$procBusName_}" BUSSTD="{$busStd}" BIFRANK="{$procBifRank_}" BIFSIDE="{$procBifSide_}"/>
										
<!--						
						<xsl:message>bcProc_X_ <xsl:value-of select="$bcProc_X_"/></xsl:message>
						<xsl:message>bcProc_Y_ <xsl:value-of select="$bcProc_Y_"/></xsl:message>
						<P2PCONN X="{$bcInSpace_X_}" Y="{$bcProc_Y_}" BUSSTD="{$busStd}" BIFRANK="{$procBifRank_}" BIFSIDE="{$procBifSide_}" STACK_ID=""/>
-->						
					</xsl:when>
									
					<xsl:otherwise>
										
						<xsl:variable name="modInstance_"     select="@INSTANCE"/>
						<xsl:variable name="modshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $modInstance_)]]/@SHAPE_VERTI_INDEX"/>
						<xsl:variable name="modBifSide_"      select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
						<xsl:variable name="modBif_Y_"        select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_Y"/>
						<xsl:variable name="modBc_Y_"         select="((($BIF_H + $MOD_BIF_GAP_V) * $modBif_Y_) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
										
<!--										
						<xsl:message>Memory Instance <xsl:value-of select="$procInstance_"/></xsl:message>
-->										
						
						<xsl:variable name="modshp_Y_">
							<xsl:call-template name="_calc_Stack_Shape_Y">
								<xsl:with-param name="horizIdx"  select="$p2pshp_hori_idx_"/>
								<xsl:with-param name="vertiIdx"  select="$modshp_vert_idx_"/>
							</xsl:call-template>
						</xsl:variable>
										
						<xsl:variable name="modBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
						<xsl:variable name="modBusName_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BUSNAME"/>
						<xsl:variable name="bcMod_Y_"     select="($modshp_Y_ + $modBc_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $cmplxStack_H_diff_)"/>
						<xsl:variable name="bcMod_X_">
							<xsl:choose>
								<xsl:when test="$modBifSide_ = '0'">
		 							<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($periMOD_W div 2) + $BIFC_W))"/>
								</xsl:when>
								<xsl:when test="$modBifSide_ = '1'">
		 							<xsl:value-of select="ceiling($periMOD_W div 2)"/>
								</xsl:when>
								<xsl:otherwise>0</xsl:otherwise>
							</xsl:choose>
						</xsl:variable>
						
<!--										
						<xsl:message>Bc Bif Y <xsl:value-of select="$modBif_Y_"/></xsl:message>	
						<xsl:message>Bc Mod Y <xsl:value-of select="$modBc_Y_"/></xsl:message>	
						<xsl:message>Bc Mod X <xsl:value-of select="$bcMod_X_"/></xsl:message>	
						<P2PCONN X="{$bcInSpace_X_}" Y="{$bcMod_Y_}" BUSSTD="{$busStd}" BIFRANK="{$modBifRank_}" BIFSIDE="{$modBifSide_}"/>
-->										
						<P2PCONN X="{$bcMod_X_}" Y="{$bcMod_Y_}" BUSNAME="{$modBusName_}" BUSSTD="{$busStd}" BIFRANK="{$modBifRank_}" BIFSIDE="{$modBifSide_}"/>
						
					</xsl:otherwise>
									
				</xsl:choose>
			</xsl:for-each>
		</xsl:variable>
	
	
	<xsl:variable name="busTop_"  select="math:min(exsl:node-set($p2pConn_heights_)/P2PCONN/@Y)"/>
	<xsl:variable name="busBot_"  select="math:max(exsl:node-set($p2pConn_heights_)/P2PCONN/@Y)"/>
	<xsl:variable name="v_bus_y_" select="$busTop_ + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
	<xsl:variable name="busName_" select="exsl:node-set($p2pConn_heights_)/P2PCONN/@BUSNAME"/>
	<xsl:variable name="busStd_"  select="exsl:node-set($p2pConn_heights_)/P2PCONN/@BUSSTD"/>
<!--	
-->	
	<!-- Draw the vertical part of the bus -->	
	
	<xsl:if test="$busStd_ = 'PLBV46_P2P'">
	<rect x="{$bcInSpace_X_ + $P2P_BUS_W}" 
	  	  y="{$v_bus_y_}"  
	 	  width= "{$P2P_BUS_W}" 
	 	  height="{($busBot_ - $busTop_) + $P2P_BUS_W}" 
	 	  style="stroke:{$COL_WHITE};stroke-width:1.5;fill:{$bus_color_}"/>
	</xsl:if>
	
	<xsl:if test="not($busStd_ = 'PLBV46_P2P')">
	<rect x="{$bcInSpace_X_ + $P2P_BUS_W}" 
	  	  y="{$v_bus_y_}"  
	 	  width= "{$P2P_BUS_W}" 
	 	  height="{($busBot_ - $busTop_) + $P2P_BUS_W}" 
	 	  style="stroke:none;fill:{$bus_color_}"/>
	</xsl:if>
	
<!--	
-->	
	
<!--	
	 	  style="stroke:{$bus_color_lt_};stroke-width:1;stroke-opacity:0.9;fill-opacity:2.0;fill:{$bus_color_}"/>
-->	
	<!-- Place the bus label.-->	
	<text class="p2pbuslabel" 
			  x="{$bcInSpace_X_   + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 6}"
			  y="{$busTop_ + ($BUS_ARROW_H * 3)}">
			<xsl:value-of select="$busName_"/>
	</text>	
						
		<!-- Draw the busconnection and horizontal lines.-->						
		<xsl:for-each select="exsl:node-set($p2pConn_heights_)/P2PCONN">
							
			<xsl:variable name="bus_x_" select="($bcInSpace_X_ + ceiling($BIFC_W div 2))"/>
			<xsl:variable name="bus_y_" select="@Y + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
		
			<xsl:variable name="h_bus_ul_x_">
				<xsl:choose>
					<xsl:when test="@BIFSIDE='0'">
						<xsl:value-of select="$bus_x_"/>
					</xsl:when>
					<xsl:when test="@BIFSIDE='1'">
						<xsl:value-of select="(@X + $BIFC_W + $BUS_ARROW_W) - 1"/>
					</xsl:when>
				</xsl:choose>
			</xsl:variable>	
		
			<xsl:variable name="h_bus_ul_y_" select="$bus_y_"/>
	
			<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
			<xsl:variable name="h_bus_width_">
<!--				
				<xsl:message>BIFSIDE <xsl:value-of select="@BIFSIDE"/></xsl:message>
				<xsl:message>BUSSTD  <xsl:value-of select="@BUSSTD"/></xsl:message>
				<xsl:message>BIFRANK <xsl:value-of select="@BIFRANK"/></xsl:message>
-->				
				<xsl:choose>
					<xsl:when test="@BIFSIDE='0'">
						<xsl:value-of select="(@X - $bus_x_ - $BUS_ARROW_W)"/>
					</xsl:when>
					<xsl:when test="@BIFSIDE='1'">
						<xsl:value-of select="$bus_x_ - $h_bus_ul_x_ + 1"/>
					</xsl:when>
					
				</xsl:choose>
			</xsl:variable>	
			
			<!-- Draw Bus connection-->
			<use   x="{@X}"   y="{@Y}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
			
			<!-- Draw the arrow -->
			<xsl:choose>
				<xsl:when test="((@BIFSIDE='0') and not((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{@X - $BUS_ARROW_W}"   y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowEast"/>
				</xsl:when>
				<xsl:when test="((@BIFSIDE='1') and not((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{(@X + $BIFC_W)}" y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowWest"/>
				</xsl:when>
				
				<xsl:when test="((@BIFSIDE='0') and ((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{@X - $BUS_ARROW_W}"   y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowHInitiator"/>
				</xsl:when>
				
				<xsl:when test="((@BIFSIDE='1') and ((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{(@X + $BIFC_W)}" y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowHInitiator"/>
				</xsl:when>
					
			</xsl:choose>
		
			<!-- Draw the horizontal part of the bus -->
			<rect x="{$h_bus_ul_x_}" 
		  	  	  y="{$h_bus_ul_y_}"  
		 	  	  width= "{$h_bus_width_}" 
		 	 	  height="{$h_bus_height_}" 
		 	      style="stroke:none; fill:{$bus_color_}"/>
		
	</xsl:for-each>
						
<!--	
	<xsl:variable name="busTop_" select="math:min(exsl:node-set($p2pConn_heights_)/P2PCONN/@Y)"/>
	<xsl:variable name="busBot_" select="math:max(exsl:node-set($p2pConn_heights_)/P2PCONN/@Y)"/>
	<xsl:variable name="v_bus_y_" select="$busTop_ + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
	<xsl:variable name="busName_" select="exsl:node-set($p2pConn_heights_)/P2PCONN/@BUSNAME"/>
-->	
	<!-- Draw the vertical part of the bus -->	
<!--	
	<rect x="{$bcInSpace_X_ + $P2P_BUS_W}" 
	  	  y="{$v_bus_y_}"  
	 	  width= "{$P2P_BUS_W}" 
	 	  height="{($busBot_ - $busTop_) + $P2P_BUS_W}" 
	 	  style="stroke:{$COL_WHITE};stroke-width:1;stroke-opacity:0.9;fill-opacity:2.0;fill:{$bus_color_}"/>
-->	
	
<!--	
	 	  style="stroke:{$bus_color_lt_};stroke-width:1;stroke-opacity:0.9;fill-opacity:2.0;fill:{$bus_color_}"/>
-->	
	<!-- Place the bus label.-->	
<!--	
	<text class="p2pbuslabel" 
			  x="{$bcInSpace_X_   + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 6}"
			  y="{$busTop_ + ($BUS_ARROW_H * 3)}">
			<xsl:value-of select="$busName_"/>
	</text>	
-->	
	
						
</xsl:template>	
	
	
					
<!-- 
		 ===========================================================
			Handle MultiStack Point to Point connections
		 ===========================================================
-->
					
<xsl:template name="BCLaneSpace_MultiStack_PointToPoint">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>							
	
					
	<!-- Store the connections in a variable -->
	<xsl:variable name="bcInSpace_X_"  select="($laneInSpace_X +  ceiling($BIFC_W div 2) - ceiling($BUS_ARROW_W div 2))"/>
					
	<xsl:variable name="multiConns_">
						
		<xsl:for-each select="BUSCONN">
							
			<xsl:variable name="bifName_"      select="@BUSINTERFACE"/>
			<xsl:variable name="multiInstance_" select="@INSTANCE"/>
			<xsl:variable name="mulshp_hori_idx_">
				<xsl:choose>
					<xsl:when test="@IS_PROCONN">
						<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $multiInstance_)]/@STACK_HORIZ_INDEX"/>
					</xsl:when>
					<xsl:otherwise>
						<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $multiInstance_)])]/@STACK_HORIZ_INDEX"/>
					</xsl:otherwise>
				</xsl:choose>
			</xsl:variable> 
							
			<xsl:variable name="mulshp_vert_idx_">
				<xsl:choose>
					<xsl:when test="@IS_PROCONN">
						<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $multiInstance_)]/@SHAPE_VERTI_INDEX"/>
					</xsl:when>
					<xsl:otherwise>
						<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $multiInstance_)])]/@SHAPE_VERTI_INDEX"/>
					</xsl:otherwise>
				</xsl:choose>
			</xsl:variable> 
				
<!--							
							<xsl:message>Shape Horiz <xsl:value-of select="$mulshp_hori_idx_"/></xsl:message>
							<xsl:message>Shape Verti <xsl:value-of select="$mulshp_vert_idx_"/></xsl:message>
-->	
							
			<xsl:variable name="mulshp_Y_">
				<xsl:call-template name="_calc_Stack_Shape_Y">
					<xsl:with-param name="horizIdx"  select="$mulshp_hori_idx_"/>
					<xsl:with-param name="vertiIdx"  select="$mulshp_vert_idx_"/>
				</xsl:call-template>
			</xsl:variable>
						
			<xsl:variable name="cmplxStack_H_diff_">
				<xsl:choose>
					<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
					<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
						
						<xsl:variable name="stackToWest_AbvSbs_H_">
							<xsl:call-template name="_calc_Stack_AbvSbs_Height">
								<xsl:with-param name="stackIdx"  select="$stkToWest"/>
							</xsl:call-template>
						</xsl:variable>
			
						<xsl:variable name="stackToEast_AbvSbs_H_">
							<xsl:call-template name="_calc_Stack_AbvSbs_Height">
								<xsl:with-param name="stackIdx"  select="$stkToEast"/>
							</xsl:call-template>
						</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
						<xsl:choose>
							<xsl:when test="(($mulshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
									<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
							</xsl:when>	
							<xsl:when test="(($mulshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
								<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
							</xsl:when>	
							<xsl:otherwise>0</xsl:otherwise>	
						</xsl:choose>	
									
					</xsl:when>
				</xsl:choose>
			</xsl:variable>
						
																				
			<xsl:variable name="procStack_H_diff_">
				<xsl:choose>
					<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
					<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
			
						<xsl:variable name="stackToWest_AbvSbs_H_">
							<xsl:call-template name="_calc_Stack_AbvSbs_Height">
								<xsl:with-param name="stackIdx"  select="$stkToWest"/>
							</xsl:call-template>
						</xsl:variable>
				
						<xsl:variable name="stackToEast_AbvSbs_H_">
							<xsl:call-template name="_calc_Stack_AbvSbs_Height">
								<xsl:with-param name="stackIdx"  select="$stkToEast"/>
							</xsl:call-template>
						</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
						<xsl:choose>
							<xsl:when test="(($mulshp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
								<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
							</xsl:when>	
							<xsl:when test="(($mulshp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
								<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
							</xsl:when>	
							<xsl:otherwise>0</xsl:otherwise>	
						</xsl:choose>	
									
					</xsl:when>
				</xsl:choose>
			</xsl:variable>
							
			<xsl:choose>
							
				<xsl:when test="@IS_PROCONN and @BIF_Y">
										
					<xsl:variable name="procBif_Y_"   select="((($BIF_H + $MOD_BIF_GAP_V) * @BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
										
					<xsl:variable name="procBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
					<xsl:variable name="procBusName_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BUSNAME"/>
					<xsl:variable name="procBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
										
					<xsl:variable name="bcProc_Y_"     select="($mulshp_Y_ + $procBif_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $procStack_H_diff_)"/>
					
					<xsl:variable name="bcProc_X_">
						<xsl:choose>
							<xsl:when test="$procBifSide_ = '0'">
		 						<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($periMOD_W div 2) + $BIFC_W))"/>
							</xsl:when>
							<xsl:when test="$procBifSide_ = '1'">
		 						<xsl:value-of select="ceiling($periMOD_W div 2)"/>
							</xsl:when>
							<xsl:otherwise>0</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
						
					<MULTICONN X="{$bcProc_X_}" Y="{$bcProc_Y_}" BUSNAME="{$procBusName_}" BUSSTD="{$busStd}" BIFRANK="{$procBifRank_}" BIFSIDE="{$procBifSide_}"/>
<!--					
					<MULTICONN X="{$bcInSpace_X_}" Y="{$bcProc_Y_}" BUSSTD="{$busStd}" BIFRANK="{$procBifRank_}" BIFSIDE="{$procBifSide_}"/>
-->					
										
				</xsl:when>
									
				<xsl:otherwise>
											
					<xsl:variable name="modType_"         select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/@MODCLASS"/>
					<xsl:variable name="modBif_Y_"        select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_Y"/>
					<xsl:variable name="modBifSide_"      select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
					
					<xsl:variable name="memcMOD_W_" select="((/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[MODULE[(@INSTANCE = $multiInstance_)]]/@MODS_W) * $periMOD_W)"/>
								
					<xsl:variable name="modBc_Y_">
						<xsl:choose>
							<xsl:when test="($modType_ = 'MEMORY_CNTLR')">
					      		<xsl:value-of select="$periMOD_H + $MOD_LANE_H + ((($BIF_H + $MOD_BIF_GAP_V) * $modBif_Y_))"/>
							</xsl:when>
							<xsl:otherwise>
					      		<xsl:value-of select="((($BIF_H + $MOD_BIF_GAP_V) * $modBif_Y_) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
							</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>   
					
					
<!--					
					<xsl:message>Multi module width <xsl:value-of select="$memcMOD_W_"/></xsl:message>
					<xsl:message>Multi instance <xsl:value-of select="$multiInstance_"/></xsl:message>
					<xsl:message>Multi instance <xsl:value-of select="$multiInstance_"/></xsl:message>
-->					
								
					<xsl:variable name="modBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
					<xsl:variable name="modBusName_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $multiInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BUSNAME"/>
					<xsl:variable name="bcMod_Y_"     select="($mulshp_Y_ + $modBc_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $cmplxStack_H_diff_)"/>
					<xsl:variable name="bcMod_X_">
						<xsl:choose>
							<xsl:when test="$modBifSide_ = '0'">
		 						<xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - (ceiling($memcMOD_W_ div 2) + $BIFC_W))"/>
							</xsl:when>
							<xsl:when test="$modBifSide_ = '1'">
		 						<xsl:value-of select="ceiling($memcMOD_W_ div 2)"/>
							</xsl:when>
							<xsl:otherwise>0</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
						
					
					<MULTICONN X="{$bcMod_X_}" Y="{$bcMod_Y_}" BUSNAME="{$modBusName_}" BUSSTD="{$busStd}" BIFRANK="{$modBifRank_}" BIFSIDE="{$modBifSide_}"/>
<!--					
					<MULTICONN X="{$bcInSpace_X_}" Y="{$bcMod_Y_}" BUSSTD="{$busStd}" BIFRANK="{$modBifRank_}" BIFSIDE="{$modBifSide_}"/>
-->					
						
					</xsl:otherwise>
				</xsl:choose>	
			</xsl:for-each>
		</xsl:variable>
					
		<!-- Draw the busconnection and horizontal lines.-->						
		<xsl:for-each select="exsl:node-set($multiConns_)/MULTICONN">
							
			<xsl:variable name="bus_x_" select="($bcInSpace_X_ + ceiling($BIFC_W div 2))"/>
			<xsl:variable name="bus_y_" select="@Y + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
		
			<xsl:variable name="h_bus_ul_x_">
				<xsl:choose>
					<xsl:when test="@BIFSIDE='0'">
						<xsl:value-of select="$bus_x_"/>
					</xsl:when>
					<xsl:when test="@BIFSIDE='1'">
						<xsl:value-of select="(@X + $BIFC_W + $BUS_ARROW_W)"/>
					</xsl:when>
				</xsl:choose>
			</xsl:variable>	
		
			<xsl:variable name="h_bus_ul_y_" select="$bus_y_"/>
	
			<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
			<xsl:variable name="h_bus_width_">
<!--				
				<xsl:message>BUSSTD  <xsl:value-of select="@BUSSTD"/></xsl:message>
				<xsl:message>BIFSIDE <xsl:value-of select="@BIFSIDE"/></xsl:message>
				<xsl:message>BIFRANK <xsl:value-of select="@BIFRANK"/></xsl:message>
-->				
				<xsl:choose>
					<xsl:when test="@BIFSIDE='0'">
						<xsl:value-of select="(@X - $bus_x_ - $BUS_ARROW_W)"/>
					</xsl:when>
					<xsl:when test="@BIFSIDE='1'">
						<xsl:value-of select="$bus_x_ - $h_bus_ul_x_"/>
					</xsl:when>
				</xsl:choose>
			</xsl:variable>		
			
			
			<!-- Draw the horizontal part of the bus -->
			<rect x="{$h_bus_ul_x_}" 
		  	  	  y="{$h_bus_ul_y_}"  
		 	  	  width= "{$h_bus_width_}" 
		 	 	  height="{$h_bus_height_}" 
		 	      style="stroke:none; fill:{$bus_color_}"/>
		
			
			<!-- Draw the arrow -->
			<xsl:choose>
				<xsl:when test="((@BIFSIDE='0') and not((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{@X - $BUS_ARROW_W}"   y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowEast"/>
				</xsl:when>
				<xsl:when test="((@BIFSIDE='1') and not((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{(@X + $BIFC_W)}" y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowWest"/>
				</xsl:when>
				
				<xsl:when test="((@BIFSIDE='0') and ((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{@X - $BUS_ARROW_W}"   y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowHInitiator"/>
				</xsl:when>
				
				<xsl:when test="((@BIFSIDE='1') and ((@BUSSTD = 'FSL') and ((@BIFRANK = 'INITIATOR') or (@BIFRANK = 'MASTER'))))">
					<use   x="{(@X + $BIFC_W)}" y="{@Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2)}"  xlink:href="#{@BUSSTD}_BusArrowHInitiator"/>
				</xsl:when>
					
			</xsl:choose>
		
			<use   x="{@X}"   y="{@Y}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
			
							
		</xsl:for-each>
						
		<xsl:variable name="busTop_" select="math:min(exsl:node-set($multiConns_)/MULTICONN/@Y)"/>
		<xsl:variable name="busBot_" select="math:max(exsl:node-set($multiConns_)/MULTICONN/@Y)"/>
<!--	
		<xsl:variable name="topRnk_" select="(exsl:node-set($multiConns_)/MULTICONN[(@Y = $busTop_)]/@BIFRANK)"/>
		<xsl:variable name="botRnk_" select="(exsl:node-set($multiConns_)/MULTICONN[(@Y = $busBot_)]/@BIFRANK)"/>
-->	
	
		<xsl:variable name="v_bus_y_" select="$busTop_ + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
		<xsl:variable name="busName_" select="exsl:node-set($multiConns_)/MULTICONN/@BUSNAME"/>
	
		<!-- Draw the vertical part of the bus -->	
		<rect x="{$bcInSpace_X_ + $P2P_BUS_W}" 
	  	  	  y="{$v_bus_y_}"  
	 	      width= "{$P2P_BUS_W}" 
	 	      height="{($busBot_ - $busTop_) + $P2P_BUS_W}" 
	 	      style="stroke:none; fill:{$bus_color_}"/>
						
	<!-- Place the bus label.-->	
		<text class="p2pbuslabel" 
			  x="{$bcInSpace_X_   + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 6}"
			  y="{$busTop_ + ($BUS_ARROW_H * 3)}">
			<xsl:value-of select="$busName_"/>
		</text>	
<!--	
-->	
	
	
	
	
<!--						
						<xsl:message>Bot Rank  <xsl:value-of select="$botRnk_"/></xsl:message>	
-->						
						
<!--	
		<xsl:call-template name="Draw_P2PBus">
			<xsl:with-param name="busX"    select="$bcInSpace_X_"/>
			<xsl:with-param name="busTop"  select="$busTop_"/>
			<xsl:with-param name="busBot"  select="$busBot_"/>
			<xsl:with-param name="topRnk"  select="$topRnk_"/>
			<xsl:with-param name="botRnk"  select="$botRnk_"/>
			<xsl:with-param name="busStd"  select="$busStd"/>
			<xsl:with-param name="busName" select="$busName"/>
		</xsl:call-template>
-->	
					
</xsl:template>	
	
	
<!-- 
		 ===========================================================
			Handle Processor to processor connections
		 ===========================================================
-->
<xsl:template name="BCLaneSpace_ProcToProc">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>							
		
	<xsl:variable name="pr2pr_stkToWest_"   select="math:min(BUSCONN/@STACK_HORIZ_INDEX)"/>
	<xsl:variable name="pr2pr_stkToEast_"   select="math:max(BUSCONN/@STACK_HORIZ_INDEX)"/>
	<xsl:variable name="proc2procConn_heights_">
	
	<xsl:for-each select="BUSCONN">
					
		<xsl:variable name="procInstance_" select="@INSTANCE"/>
		<xsl:variable name="bifName_"      select="@BUSINTERFACE"/>
		<xsl:variable name="procshp_hori_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInstance_)]/@STACK_HORIZ_INDEX"/>
		<xsl:variable name="procshp_vert_idx_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInstance_)]/@SHAPE_VERTI_INDEX"/>
		<xsl:variable name="procshp_Y_">
			<xsl:call-template name="_calc_Stack_Shape_Y">
				<xsl:with-param name="horizIdx"  select="$procshp_hori_idx_"/>
				<xsl:with-param name="vertiIdx"  select="$procshp_vert_idx_"/>
			</xsl:call-template>
		</xsl:variable>
						
		<xsl:variable name="procStack_H_diff_">
			<xsl:choose>
				<xsl:when test="   (($pr2pr_stkToEast_ = 'NONE') or ($pr2pr_stkToWest_ = 'NONE'))">0</xsl:when>
				<xsl:when test="not(($pr2pr_stkToEast_ = 'NONE') or ($pr2pr_stkToWest_ = 'NONE'))">
			
					<xsl:variable name="stackToWest_AbvSbs_H_">
						<xsl:call-template name="_calc_Stack_AbvSbs_Height">
							<xsl:with-param name="stackIdx"  select="$pr2pr_stkToWest_"/>
						</xsl:call-template>
					</xsl:variable>
				
					<xsl:variable name="stackToEast_AbvSbs_H_">
						<xsl:call-template name="_calc_Stack_AbvSbs_Height">
							<xsl:with-param name="stackIdx"  select="$pr2pr_stkToEast_"/>
						</xsl:call-template>
					</xsl:variable>
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
					<xsl:choose>
						<xsl:when test="(($procshp_hori_idx_ = $pr2pr_stkToEast_) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
							<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
						</xsl:when>	
						<xsl:when test="(($procshp_hori_idx_ = $pr2pr_stkToWest_) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
							<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
						</xsl:when>	
						<xsl:otherwise>0</xsl:otherwise>	
					</xsl:choose>	
										
				</xsl:when>
			</xsl:choose>
		</xsl:variable>
						
		<!-- Store the conns in a variable -->	
		<xsl:variable name="procBif_Y_"   select="((($BIF_H + $MOD_BIF_GAP_V) * @BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
											
		<xsl:variable name="procBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
		<xsl:variable name="procBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
									
		<xsl:variable name="bcInSpace_X_">
			<xsl:choose>
				<xsl:when test="$procBifSide_ = '1'"><xsl:value-of select="ceiling($periMOD_W div 2)"/></xsl:when>
				<xsl:when test="$procBifSide_ = '0'"><xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - ceiling($periMOD_W div 2) - $BIFC_W)"/></xsl:when>
			</xsl:choose>
		</xsl:variable> 
							
		<xsl:variable name="bcProc_Y_"     select="($procshp_Y_ + $procBif_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $procStack_H_diff_)"/>
						
							
<!--							
							<xsl:message>Conn X <xsl:value-of select="$bcInSpace_X_"/></xsl:message>
							<xsl:message>Conn Y <xsl:value-of select="$bcProc_Y_"/></xsl:message>
-->							
										
				<PR2PRCONN X="{$bcInSpace_X_}" Y="{$bcProc_Y_}" BUSSTD="{$busStd}" BIFRANK="{$procBifRank_}" BIFSIDE="{$procBifSide_}" SHAPE_ID="{$procshp_hori_idx_}"/>
			</xsl:for-each>
		</xsl:variable>
					
		<xsl:variable name="pr2prLeft_"   select="math:min(exsl:node-set($proc2procConn_heights_)/PR2PRCONN/@SHAPE_ID)"/>
		<xsl:variable name="pr2prRght_"   select="math:max(exsl:node-set($proc2procConn_heights_)/PR2PRCONN/@SHAPE_ID)"/>
				
		<xsl:variable name="pr2pr_stack_Left_X_">
			<xsl:call-template name="_calc_Stack_X"> 
				<xsl:with-param name="stackIdx"  select="$pr2prLeft_"/>
			</xsl:call-template>		
		</xsl:variable>	
					
		<xsl:variable name="pr2pr_stack_Rght_X_">
			<xsl:call-template name="_calc_Stack_X"> 
				<xsl:with-param name="stackIdx"  select="$pr2prRght_"/>
			</xsl:call-template>		
		</xsl:variable>	
					
<!--					
					<xsl:message>Left stack X <xsl:value-of select="$pr2pr_stack_Left_X_"/></xsl:message>
					<xsl:message>Rght stack X <xsl:value-of select="$pr2pr_stack_Rght_X_"/></xsl:message>
-->					
		<xsl:variable name="pr2pr_space_W_" select="($pr2pr_stack_Rght_X_ - $pr2pr_stack_Left_X_)"/>
						
					
		<xsl:variable name="pr2pr_extStackEast_W_">
			<xsl:call-template name="_calc_Stack_Width">
				<xsl:with-param name="stackIdx"  select="$pr2prRght_"/>
			</xsl:call-template>
		</xsl:variable>
					
		<xsl:variable name="pr2pr_extStackWest_W_">
			<xsl:call-template name="_calc_Stack_Width">
				<xsl:with-param name="stackIdx"  select="$pr2prLeft_"/>
			</xsl:call-template>
		</xsl:variable>
					
<!--					
					<xsl:message>Space W <xsl:value-of select="$pr2pr_space_W_"/></xsl:message>
					<xsl:message>Rght stack <xsl:value-of select="$pr2pr_extStackEast_W_"/></xsl:message>
					<xsl:message>Left stack <xsl:value-of select="$pr2pr_extStackWest_W_"/></xsl:message>
-->					
	
		<xsl:variable name="connLeft_X_" select="ceiling($periMOD_W div 2)"/>
		<xsl:variable name="connRght_X_" select="($pr2pr_space_W_ - ceiling($pr2pr_extStackWest_W_ div 2) + ceiling($pr2pr_extStackEast_W_ div 2) - ceiling($periMOD_W div 2) - $BIFC_W)"/>
					
					<!-- Draw the busconnections .-->						
		<xsl:for-each select="exsl:node-set($proc2procConn_heights_)/PR2PRCONN">
			<xsl:variable name="conn_X_">
				<xsl:choose>
					<xsl:when test="@BIFSIDE = '1'"><xsl:value-of select="ceiling($periMOD_W div 2)"/></xsl:when>
					<xsl:when test="@BIFSIDE = '0'"><xsl:value-of select="($pr2pr_space_W_ - ceiling($pr2pr_extStackWest_W_ div 2) + ceiling($pr2pr_extStackEast_W_ div 2) - ceiling($periMOD_W div 2) - $BIFC_W)"/></xsl:when>
<!--									
									<xsl:when test="@BIFSIDE = '0'"><xsl:value-of select="($pr2pr_space_W_ + $pr2pr_extStackWest_W_ + $pr2pr_extStackEast_W_ - ceiling($periMOD_W div 2) - $BIFC_W)"/></xsl:when>
-->	
				</xsl:choose>
			</xsl:variable> 
							
						
			<use   x="{$conn_X_}"   y="{@Y}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
		</xsl:for-each>
					
		<xsl:variable name="bc_Y_"     select="math:min(exsl:node-set($proc2procConn_heights_)/PR2PRCONN/@Y)"/>
		<xsl:variable name="bcLeft_"   select="math:min(exsl:node-set($proc2procConn_heights_)/PR2PRCONN/@X)"/>
		<xsl:variable name="bcRght_"   select="math:max(exsl:node-set($proc2procConn_heights_)/PR2PRCONN/@X)"/>
					
		<xsl:variable name="leftRnk_"  select="(exsl:node-set($proc2procConn_heights_)/PR2PRCONN[(@X = $bcLeft_)]/@BIFRANK)"/>
		<xsl:variable name="rghtRnk_"  select="(exsl:node-set($proc2procConn_heights_)/PR2PRCONN[(@X = $bcRght_)]/@BIFRANK)"/>
						
		<xsl:call-template name="Draw_Proc2ProcBus">
			<xsl:with-param name="bc_Y"     select="$bc_Y_"/>
			<xsl:with-param name="bcLeft_X" select="$connLeft_X_ + $BIFC_W"/>
			<xsl:with-param name="bcRght_X" select="$connRght_X_"/>
			<xsl:with-param name="leftRnk"  select="$leftRnk_"/>
			<xsl:with-param name="rghtRnk"  select="$rghtRnk_"/>
			<xsl:with-param name="busStd"   select="$busStd"/>
			<xsl:with-param name="busName"  select="$busName"/>
		</xsl:call-template>
				
</xsl:template>	
	
				
<!-- 
		 ===========================================================
			Handle Split connections, (connections that go between adjacent stacks)
		 ===========================================================
-->
	
<xsl:template name="BCLaneSpace_SplitConn">	
	
	<xsl:param name="sbs_Y"         select="0"/>	
	<xsl:param name="stkToEast"     select="'NONE'"/>	
	<xsl:param name="stkToWest"     select="'NONE'"/>	
	<xsl:param name="stkToEast_W"   select="0"/>	
	<xsl:param name="stkToWest_W"   select="0"/>	
	<xsl:param name="busStd"        select="'NONE'"/>	
	<xsl:param name="busName"       select="'NONE'"/>	
	<xsl:param name="bifRank"       select="'NONE'"/>	
	<xsl:param name="laneInSpace_X" select="0"/>	
	
	<xsl:variable name="bus_color_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>	
	
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stkToEast"/>
			<xsl:with-param name="stackToWest"  select="$stkToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stkToWest_W div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stkToEast_W div 2)"/>							
			
					
	<xsl:variable name="bifName_"      select="BUSCONN/@BUSINTERFACE"/>
	<xsl:variable name="shpInstance_"  select="BUSCONN/@INSTANCE"/>
					
<!--					
			<xsl:message>Found a split connection on <xsl:value-of select="$shpInstance_"/></xsl:message>	
-->					
						
					
		<xsl:variable name="shp_hori_idx_">
						
			<xsl:choose>
				<xsl:when  test="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $shpInstance_)]">
					<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $shpInstance_)]/@STACK_HORIZ_INDEX"/>
				</xsl:when>
							
				<xsl:when  test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $shpInstance_)])]">
					<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $shpInstance_)])]/@STACK_HORIZ_INDEX"/>
				</xsl:when>
				<xsl:otherwise>_unknown_</xsl:otherwise>
			</xsl:choose>		
						
		</xsl:variable> 
					
		<xsl:variable name="shp_vert_idx_">
						
			<xsl:choose>
				<xsl:when  test="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $shpInstance_)]">
					<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $shpInstance_)]/@SHAPE_VERTI_INDEX"/>
				</xsl:when>
							
				<xsl:when  test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $shpInstance_)])]">
					<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $shpInstance_)])]/@SHAPE_VERTI_INDEX"/>
				</xsl:when>
				<xsl:otherwise>_unknown_</xsl:otherwise>
			</xsl:choose>		
						
		</xsl:variable> 
					
		<xsl:variable name="splitshp_Width_">
						
			<xsl:choose>
				<xsl:when  test="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $shpInstance_)]">
					<xsl:value-of select="$periMOD_W"/>
				</xsl:when>
						
				<xsl:when  test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $shpInstance_)])]/@MODS_W">
<!--								
								<xsl:message>Using mods width on <xsl:value-of select="$shpInstance_"/></xsl:message>
-->								
					<xsl:value-of select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(MODULE[(@INSTANCE = $shpInstance_)])]/@MODS_W * $periMOD_W)"/>
				</xsl:when>
				<xsl:otherwise>
					<xsl:value-of select="$periMOD_W"/>
				</xsl:otherwise>
			</xsl:choose>		
						
		</xsl:variable> 
					
<!--					
					<xsl:message>Found width of <xsl:value-of select="$splitshp_Width_"/></xsl:message>
-->					
	
					
		<xsl:variable name="splitshp_Y_">
			<xsl:call-template name="_calc_Stack_Shape_Y">
				<xsl:with-param name="horizIdx"  select="$shp_hori_idx_"/>
				<xsl:with-param name="vertiIdx"  select="$shp_vert_idx_"/>
			</xsl:call-template>
		</xsl:variable>
					
						
		<xsl:variable name="splitStack_H_diff_">
			<xsl:choose>
				<xsl:when test="   (($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">0</xsl:when>
				<xsl:when test="not(($stkToEast = 'NONE') or ($stkToWest = 'NONE'))">
	
					<xsl:variable name="stackToWest_AbvSbs_H_">
						<xsl:call-template name="_calc_Stack_AbvSbs_Height">
							<xsl:with-param name="stackIdx"  select="$stkToWest"/>
						</xsl:call-template>
					</xsl:variable>
				
					<xsl:variable name="stackToEast_AbvSbs_H_">
						<xsl:call-template name="_calc_Stack_AbvSbs_Height">
							<xsl:with-param name="stackIdx"  select="$stkToEast"/>
						</xsl:call-template>
					</xsl:variable>
				
<!--				
				<xsl:message>stack to west H <xsl:value-of select="$stackToWest_AbvSbs_H_"/></xsl:message>
				<xsl:message>stack to east H <xsl:value-of select="$stackToEast_AbvSbs_H_"/></xsl:message>
-->				
					<xsl:choose>
						<xsl:when test="(($shp_hori_idx_ = $stkToEast) and ($stackToWest_AbvSbs_H_ &gt; $stackToEast_AbvSbs_H_))">
							<xsl:value-of select="($stackToWest_AbvSbs_H_ - $stackToEast_AbvSbs_H_)"/>
						</xsl:when>	
						<xsl:when test="(($shp_hori_idx_ = $stkToWest) and ($stackToEast_AbvSbs_H_ &gt; $stackToWest_AbvSbs_H_))">
							<xsl:value-of select="($stackToEast_AbvSbs_H_ - $stackToWest_AbvSbs_H_)"/>
						</xsl:when>	
						<xsl:otherwise>0</xsl:otherwise>	
					</xsl:choose>	
										
				</xsl:when>
			</xsl:choose>
		</xsl:variable>
						
					
		<xsl:variable name="splitBif_Y_"    select="((($BIF_H + $MOD_BIF_GAP_V) * BUSCONN/@BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
		<xsl:variable name="splitBifRank_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $shpInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIFRANK"/>
		<xsl:variable name="splitBifSide_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $shpInstance_)]/BUSINTERFACE[(@NAME = $bifName_)]/@BIF_X"/>
									
		<xsl:variable name="bcInSpace_X_">
			<xsl:choose>
				<xsl:when test="$splitBifSide_ = '1'"><xsl:value-of select="ceiling($splitshp_Width_ div 2)"/></xsl:when>
				<xsl:when test="$splitBifSide_ = '0'"><xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - ceiling($splitshp_Width_ div 2) - $BIFC_W)"/></xsl:when>
			</xsl:choose>
								
		</xsl:variable> 
					
		<xsl:variable name="bcBus_X_">
			<xsl:choose>
				<xsl:when test="$splitBifSide_ = '1'"><xsl:value-of select="$bcInSpace_X_"/></xsl:when>
				<xsl:when test="$splitBifSide_ = '0'"><xsl:value-of select="($space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_ - ceiling($periMOD_W div 2) - $BIFC_W)"/></xsl:when>
			</xsl:choose>
		</xsl:variable> 
							
		<xsl:variable name="bcSplit_Y_">
			<xsl:choose>
				<xsl:when test="(BUSCONN/@IS_MEMCONN)">
<!--								
								<xsl:message>Found memory conn split connection on <xsl:value-of select="$shpInstance_"/> </xsl:message>
-->	
					<xsl:value-of select="($splitshp_Y_ + $periMOD_H + $MOD_BIF_GAP_V + (BUSCONN/@BIF_Y * ($BIF_H + $MOD_BIF_GAP_V)) + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $splitStack_H_diff_)"/>
				</xsl:when>     
				<xsl:otherwise>
					<xsl:value-of select="($splitshp_Y_ + $splitBif_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $splitStack_H_diff_)"/>
				</xsl:otherwise>
			</xsl:choose>
		</xsl:variable>    
<!--								
								<xsl:value-of select="($splitshp_Y_ + $splitBif_Y_ + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2) + $splitStack_H_diff_)"/>
-->								
<!--					
					<xsl:message>VERTI INDEX <xsl:value-of select="$shp_vert_idx_"/></xsl:message>	
					<xsl:message>BIF Y <xsl:value-of select="$splitBif_Y_"/></xsl:message>	
					<xsl:message>HORIZ INDEX <xsl:value-of select="$shp_hori_idx_"/></xsl:message>	
-->					
					
	<use   x="{$bcInSpace_X_}"   y="{$bcSplit_Y_}"  xlink:href="#{@BUSSTD}_busconn_{$splitBifRank_}"/>
					
			
	<xsl:call-template name="Draw_SplitConnBus">
		<xsl:with-param name="bc_Y"    select="$bcSplit_Y_"/>
		<xsl:with-param name="bc_X"    select="$bcInSpace_X_"/>
						
		<xsl:with-param name="bc_Rnk"  select="$splitBifRank_"/>
		<xsl:with-param name="bc_Side" select="$splitBifSide_"/>
						
		<xsl:with-param name="busStd"  select="$busStd"/>
		<xsl:with-param name="busName" select="$busName"/>
	</xsl:call-template>
					
	
</xsl:template>	
	
	
<xsl:template name="Define_BusLaneSpace"> 
	
	<xsl:param name="stackToEast"  select="'NONE'"/>
	<xsl:param name="stackToWest"  select="'NONE'"/>
	
	<xsl:variable name="stkToEast_">
		<xsl:choose>
			<xsl:when test="not($stackToEast = 'NONE')"><xsl:value-of select="$stackToEast"/></xsl:when>
<!--			
			<xsl:when test="not($stackToWest = 'NONE')"><xsl:value-of select="($stackToWest + 1)"/></xsl:when>
-->	
			<xsl:otherwise>NONE</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>	
	
	<xsl:variable name="stkToWest_">
		<xsl:choose>
			<xsl:when test="not($stackToWest  = 'NONE')"><xsl:value-of select="$stackToWest"/></xsl:when>
			<xsl:when test="(not($stackToEast = 'NONE') and not($stackToEast = '0'))"><xsl:value-of select="($stackToEast - 1)"/></xsl:when>
			<xsl:otherwise>NONE</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>	
	
<!--	
	<xsl:message>Stack to West <xsl:value-of select="$stackToWest"/></xsl:message>
	<xsl:message>Stack to East <xsl:value-of select="$stackToEast"/></xsl:message>
-->	
	
<!--	
	<xsl:message>Stack abv diff  <xsl:value-of select="$stack_H_diff_"/></xsl:message>
-->	
	
	<xsl:variable name="spaceAbvSbs_H_">
		<xsl:call-template name="_calc_Space_AbvSbs_Height">
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>
	</xsl:variable>	
	
	<xsl:variable name="spaceBlwSbs_H_">
		<xsl:call-template name="_calc_Space_BlwSbs_Height">
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>
	</xsl:variable>	
	
	<xsl:variable name="numSbs_"      select="count(/EDKSYSTEM/BLKDSHAPES/SBSSHAPES/MODULE)"/>	
	<xsl:variable name="totalSbs_H_"  select="($numSbs_ * $SBS_LANE_H)"/>
	
	<xsl:variable name="space_H_" select="($spaceAbvSbs_H_ + $PROC2SBS_GAP + $totalSbs_H_ + $spaceBlwSbs_H_)"/>
	<xsl:variable name="space_W_">
		<xsl:call-template name="_calc_Space_Width"> 
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
<!--	
	<xsl:variable name="sbs_Y_" select="$spaceAbvSbs_H_ + $BIF_H"/>
-->	
	
	<xsl:variable name="sbs_Y_" select="$spaceAbvSbs_H_ + $PROC2SBS_GAP"/>
	
	<xsl:variable name="space_name_">
		<xsl:call-template name="_gen_Space_Name"> 
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>		
	</xsl:variable>
	
	
<!--	
	<xsl:message>Stack Width <xsl:value-of select="$space_W_"/></xsl:message>
	<xsl:message>Space Name <xsl:value-of select="$space_name_"/></xsl:message>
	<xsl:message>Stack Abv <xsl:value-of select="$spaceAbvSbs_H_"/></xsl:message>
	<xsl:message>Stack Blw <xsl:value-of select="$spaceBlwSbs_H_"/></xsl:message>
	<xsl:message>Total Sbs <xsl:value-of select="$totalSbs_H_"/></xsl:message>
-->	
	
	<xsl:variable name = "stackToWest_W_">
		<xsl:choose>
			<xsl:when test="(($stackToEast = '0')   and     ($stackToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="(($stackToEast = 'NONE') and not($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_Width">
					<xsl:with-param name="stackIdx"  select="$stackToWest"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:when test="(not($stackToEast = '0') and not($stackToEast = 'NONE') and ($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_Width">
					<xsl:with-param name="stackIdx"  select="($stackToEast - 1)"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:otherwise>0</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name = "stackToEast_W_">
		<xsl:call-template name="_calc_Stack_Width">
			<xsl:with-param name="stackIdx"  select="$stackToEast"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stackToWest_W_ div 2)"/>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stackToEast_W_ div 2)"/>
	
<!--	
	<xsl:message>Stack To West <xsl:value-of select="$stackToWest_W_"/></xsl:message>
	<xsl:message>Stack To East <xsl:value-of select="$stackToEast_W_"/></xsl:message>
-->	
	
	<symbol id="{$space_name_}">
<!--		
		
		<xsl:if test="not($stackToEast = 'NONE')">
		<rect x="0"
			  y="0"
	          width = "{$space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_}"
		      height= "{$space_H_}"
			  style="fill:{$COL_YELLOW}; stroke:none;"/>
		</xsl:if>
		
		<xsl:if test="not($stackToWest = 'NONE')">
		<rect x="0"
			  y="0"
	          width = "{$space_W_ + $extSpaceWest_W_ + $extSpaceEast_W_}"
		      height= "{$space_H_}"
			  style="fill:{$COL_WHITE}; stroke:none;"/>
		</xsl:if>
-->		
		
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[((@EAST = $stackToEast) or (($stackToEast = 'NONE') and (@WEST = $stackToWest)))]/BUSCONNLANE[@BUSSTD and @BUSNAME]">
				
<!--				
				<xsl:message>Bus Std of conn <xsl:value-of select="@BUSSTD"/></xsl:message>
-->				
				<xsl:variable name="busStd_"          select="@BUSSTD"/>
				<xsl:variable name="busName_"         select="@BUSNAME"/>
				<xsl:variable name="lane_X_"          select="@BUSLANE_X"/>
				<xsl:variable name="laneInSpace_X_"   select="($extSpaceWest_W_ + ($lane_X_ * $BUS_LANE_W))"/>
				
				<xsl:variable name="bus_color_">
					<xsl:call-template name="BusType2Color">
						<xsl:with-param name="busType" select="@BUSSTD"/>
					</xsl:call-template>	
				</xsl:variable>
				
				<xsl:choose>
					
<!-- 
		 ===========================================================
			Handle Bucket connections to the shared busses.
		 ===========================================================
-->
					<xsl:when test="@BUSLANE_X and @IS_BKTCONN and BUSCONN[@BIFRANK] and /EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $busName_)]/@BUSINDEX">
						
						<xsl:call-template name="BCLaneSpace_BucketToSharedBus">
							<xsl:with-param name="busName"      select="$busName_"/>
							<xsl:with-param name="busStd"       select="$busStd_"/>
							<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
							<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
							<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
							<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
							<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
							<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
							<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
						</xsl:call-template>	
						
					</xsl:when>
					
					
<!--
		 ===========================================================
			Handle Processor's Shared bus connections.
		 ===========================================================
-->
					<xsl:when test="@BUSLANE_X and @IS_SBSCONN and BUSCONN[@BIF_Y and @IS_PROCONN and @INSTANCE and @BUSINTERFACE] and /EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $busName_)]/@BUSINDEX">
						<xsl:call-template name="BCLaneSpace_ProcBifToSharedBus">
							<xsl:with-param name="busName"      select="$busName_"/>
							<xsl:with-param name="busStd"       select="$busStd_"/>
							<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
							<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
							<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
							<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
							<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
							<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
							<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
						</xsl:call-template>	
					</xsl:when>	
					
					
<!--
		 ===========================================================
			Handle non Processor Sharedebus connections.
		 ===========================================================
-->
					<xsl:when test="@BUSLANE_X and @IS_SBSCONN and BUSCONN[@BIF_Y and not(@IS_PROCONN) and @INSTANCE and @BUSINTERFACE] and /EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $busName_)]/@BUSINDEX">
						<xsl:call-template name="BCLaneSpace_NonProcBifToSharedBus">
							<xsl:with-param name="busName"      select="$busName_"/>
							<xsl:with-param name="busStd"       select="$busStd_"/>
							<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
							<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
							<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
							<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
							<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
							<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
							<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
						</xsl:call-template>	
					</xsl:when>					
					
					
<!-- 
		 ===========================================================
			Handle connections from processors to Memory UNITs
		 ===========================================================
-->			
					<xsl:when test="@BUSLANE_X and @IS_MEMCONN and not(@IS_MULTISTK) and BUSCONN[@BIF_Y and @IS_PROCONN and not(@IS_SPLITCONN) and @INSTANCE and @BUSINTERFACE]">
						<xsl:call-template name="BCLaneSpace_ProcBifToMemoryUnit">
							<xsl:with-param name="busName"      select="$busName_"/>
							<xsl:with-param name="busStd"       select="$busStd_"/>
							<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
							<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
							<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
							<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
							<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
							<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
							<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
						</xsl:call-template>	
					</xsl:when>				
				
					
<!-- 
		 ===========================================================
			Handle generic Point to Point connections
		 ===========================================================
-->
					
				<xsl:when test="@BUSLANE_X and not(@IS_MULTISTK) and not(@IS_MEMCONN) and not(@IS_SBSCONN) and BUSCONN[@BIF_Y and @INSTANCE and @BUSINTERFACE and not(@IS_SPLITCONN)]">
						
						<xsl:call-template name="BCLaneSpace_PointToPoint">
							<xsl:with-param name="busName"      select="$busName_"/>
							<xsl:with-param name="busStd"       select="$busStd_"/>
							<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
							<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
							<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
							<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
							<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
							<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
							<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
						</xsl:call-template>	
					</xsl:when>				
				
					
<!-- 
		 ===========================================================
			Handle MultiStack Point to Point connections
		 ===========================================================
-->
					
				<xsl:when test="@BUSLANE_X and (@IS_MULTISTK) and not(@IS_SBSCONN) and BUSCONN[@BIF_Y and @IS_PROCONN and @INSTANCE and @BUSINTERFACE]">

					<xsl:call-template name="BCLaneSpace_MultiStack_PointToPoint">
							<xsl:with-param name="busName"      select="$busName_"/>
							<xsl:with-param name="busStd"       select="$busStd_"/>
							<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
							<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
							<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
							<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
							<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
							<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
							<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
						</xsl:call-template>	
					</xsl:when>				
				
						
<!-- 
		 ===========================================================
			Handle Processor to processor connections
		 ===========================================================
-->
			<xsl:when test="(@IS_PROC2PROC and (count(BUSCONN[@BIF_Y and @INSTANCE and @BUSINTERFACE]) = 2))">
					
					<xsl:call-template name="BCLaneSpace_ProcToProc">
						<xsl:with-param name="busName"      select="$busName_"/>
						<xsl:with-param name="busStd"       select="$busStd_"/>
						<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
						<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
						<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
						<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
						<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
						<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
						<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
					</xsl:call-template>	
				
			</xsl:when>
					
					
					
<!-- 
		 ===========================================================
			Handle Split connections, (connections that go between adjacent stacks)
		 ===========================================================
-->
			<xsl:when test="(BUSCONN[@BIF_Y and @INSTANCE and @BUSINTERFACE and @IS_SPLITCONN])">
				<xsl:call-template name="BCLaneSpace_SplitConn">
					<xsl:with-param name="busName"      select="$busName_"/>
					<xsl:with-param name="busStd"       select="$busStd_"/>
					<xsl:with-param name="bifRank"      select="BUSCONN/@BIFRANK"/>
					<xsl:with-param name="sbs_Y"        select="$sbs_Y_"/>
					<xsl:with-param name="stkToEast"    select="$stkToEast_"/>
					<xsl:with-param name="stkToWest"    select="$stkToWest_"/>
					<xsl:with-param name="stkToEast_W"  select="$stackToEast_W_"/>
					<xsl:with-param name="stkToWest_W"  select="$stackToWest_W_"/>
					<xsl:with-param name="laneInSpace_X"      select="$laneInSpace_X_"/>
				</xsl:call-template>	
			</xsl:when>
					
		</xsl:choose>
								
	</xsl:for-each>
		
	</symbol>
			
</xsl:template>	
	
<xsl:template name="Define_BusLaneSpaces"> 
	
	<xsl:variable name="lastStack_" select="(/EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH) - 1"/>
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[@EAST]">
		<xsl:sort select="@EAST" data-type="number"/>
			
		<xsl:call-template name="Define_BusLaneSpace">
			<xsl:with-param name="stackToEast"  select="@EAST"/>
		</xsl:call-template>
	</xsl:for-each>	
	
<!--	
	<xsl:message>Last Stack <xsl:value-of select="$lastStack_"/></xsl:message>
-->	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@WEST = $lastStack_)]">
		<xsl:call-template name="Define_BusLaneSpace">
			<xsl:with-param name="stackToWest"  select="$lastStack_"/>
		</xsl:call-template>
	</xsl:for-each>	
			
</xsl:template>
		
	
	
	
</xsl:stylesheet>