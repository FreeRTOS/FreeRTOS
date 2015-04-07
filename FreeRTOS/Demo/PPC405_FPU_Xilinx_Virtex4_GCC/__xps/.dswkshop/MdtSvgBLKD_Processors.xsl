<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:math="http://exslt.org/math"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink"
           extension-element-prefixes="math">
           
<xsl:output method="xml" 
			version="1.0" 
			encoding="UTF-8" 
			indent="yes"
	        doctype-public="-//W3C//DTD SVG 1.0//EN"
		    doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
			

<!-- ======================= DEF BLOCK =================================== -->
<xsl:template name="Define_AllStacks"> 
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@EAST &lt; /EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH)]">
			
		<xsl:call-template name="Define_Stack">
			<xsl:with-param name="iStackIdx"  select="@EAST"/>
		</xsl:call-template>
		
	</xsl:for-each>	
</xsl:template>
	
	
<xsl:template name="Define_Stack"> 
	<xsl:param name="iStackIdx"  select="100"/>
	
	<!-- Define the stack's peripheral shapes-->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $iStackIdx) and not(@MODCLASS = 'MEMORY_UNIT'))]"> 
			
		<xsl:for-each select="MODULE">
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$modInst_)]/@MODTYPE"/>
			<xsl:call-template name="Define_Peripheral"> 
				<xsl:with-param name="iModInst"    select="$modInst_"/>
				<xsl:with-param name="iModType"    select="$modType_"/>
				<xsl:with-param name="iShapeId"    select="../@SHAPE_ID"/>
				<xsl:with-param name="iHorizIdx"   select="../@STACK_HORIZ_INDEX"/>
				<xsl:with-param name="iVertiIdx"   select="../@SHAPE_VERTI_INDEX"/>
			</xsl:call-template>		
		</xsl:for-each>	
		
	</xsl:for-each>
	
	<!-- Define the stack's memory shapes-->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $iStackIdx) and (@MODCLASS='MEMORY_UNIT'))]">
		<xsl:call-template name="Define_MemoryUnit"> 
			<xsl:with-param name="iShapeId"  select="@SHAPE_ID"/>
		</xsl:call-template>
	</xsl:for-each>
	
	
	<!-- Define the stack's processors-->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE and @BIFS_W and @BIFS_H and (@STACK_HORIZ_INDEX = $iStackIdx)]">	
		<xsl:call-template name="Define_Processor"/>		
	</xsl:for-each>	
		
	<!-- Make an inventory of all the things in this processor's stack -->
	<xsl:variable name="pstackW_">
		<xsl:call-template name="_calc_Stack_Width"> 
			<xsl:with-param name="iStackIdx"  select="$iStackIdx"/>
		</xsl:call-template>		
	</xsl:variable>
		
	<xsl:variable name="pstackH_">
		<xsl:call-template name="_calc_Stack_Height"> 
			<xsl:with-param name="iStackIdx"  select="$iStackIdx"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name="procW_"    select="$BLKD_MOD_W"/>
	<xsl:variable name="procX_"    select="(ceiling($pstackW_ div 2) - ceiling($procW_ div 2))"/>
	
	
	<xsl:variable name="sbsGap_"   select="($BLKD_PROC2SBS_GAP + $G_total_SharedBus_H)"/>

	<xsl:variable name="stack_name_">
		<xsl:call-template name="_gen_Stack_Name"> 
			<xsl:with-param name="iHorizIdx" select="$iStackIdx"/>
		</xsl:call-template>		
	</xsl:variable>	
	
<!--	
		<xsl:message>Horiz index<xsl:value-of select="$stackIdx"/></xsl:message>
		<xsl:message>Drawing stack <xsl:value-of select="$stack_name_"/></xsl:message>
-->	
		
		<!-- Now use all this stuff to draw the stack-->	
		<symbol id="{$stack_name_}">
			<rect x="0"
				  y="0"
			      rx="6" 
			      ry="6" 
		          width = "{$pstackW_}"
		          height= "{$pstackH_}"
			      style="fill:{$COL_BG}; stroke:none;"/>
			
		
			<!-- First draw the the processor's peripherals-->	
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@STACK_HORIZ_INDEX = $iStackIdx)]">
				<xsl:sort select="@STACK_VERTI_INDEX" data-type="number"/>
				
				
				<xsl:variable name="shapeW_"    select="(@MODS_W * $BLKD_MOD_W)"/>
				<xsl:variable name="shapeX_"    select="(ceiling($pstackW_ div 2) - ceiling($shapeW_ div 2))"/>
				
				<xsl:variable name="stack_SymName_">
					<xsl:call-template name="_gen_Stack_SymbolName"> 
						<xsl:with-param name="iHorizIdx" select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="iVertiIdx" select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>		
				</xsl:variable>
				
<!--				
				<xsl:message>Drawing stack peripheral <xsl:value-of select="$stack_SymName_"/></xsl:message>
-->				
				<xsl:variable name="shapeY_">
					<xsl:call-template name="_calc_Stack_Shape_Y">
						<xsl:with-param name="iHorizIdx"  select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="iVertiIdx"  select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>
				</xsl:variable>  
				
			 	<use   x="{$shapeX_}"  y="{$shapeY_}"  xlink:href="#{$stack_SymName_}"/> 
			
			</xsl:for-each>
			
			
			<!-- Then draw the slave buckets for the shared busses that this processor is master to -->	
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX = $iStackIdx)]">	
				<xsl:sort select="@SHAPE_VERTI_INDEX" data-type="number"/>
			
				<xsl:variable name="bucketW_"   select="(($BLKD_MOD_BKTLANE_W * 2) + (($BLKD_MOD_W * @MODS_W) + ($BLKD_MOD_BUCKET_G * (@MODS_W - 1))))"/>
				<xsl:variable name="bucketX_"   select="(ceiling($pstackW_ div 2) - ceiling($bucketW_ div 2))"/>
				
				<xsl:variable name="bucketY_">
					<xsl:call-template name="_calc_Stack_Shape_Y">
						<xsl:with-param name="iHorizIdx"  select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="iVertiIdx"  select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>
				</xsl:variable>  
				
<!--				
				<xsl:message>SBS Bucket Y <xsl:value-of select="$bucketY_"/></xsl:message>
-->				
				
				 <use  x="{$bucketX_}"  y="{$bucketY_}"  xlink:href="#sbsbucket_{@BUSNAME}"/> 
				 
				 <text class="ipclass"
					   x="{$bucketX_}" 
					   y="{$bucketY_ - 4}">SLAVES OF <xsl:value-of select="@BUSNAME"/></text>	
			</xsl:for-each>
			
			<!-- Then draw the the processor itself -->	
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@STACK_HORIZ_INDEX = $iStackIdx)]">
				<xsl:sort select="@SHAPE_VERTI_INDEX" data-type="number"/>
				
				<xsl:variable name="procY_">
					<xsl:call-template name="_calc_Stack_Shape_Y">
						<xsl:with-param name="iHorizIdx"  select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="iVertiIdx"  select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>
				</xsl:variable>  
				
				<xsl:variable name="stack_SymName_">
					<xsl:call-template name="_gen_Stack_SymbolName"> 
						<xsl:with-param name="iHorizIdx" select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="iVertiIdx" select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>		
				</xsl:variable>
				
			 	<use   x="{$procX_}"  y="{$procY_}"  xlink:href="#{$stack_SymName_}"/> 
				
				<xsl:if test = "not(@IS_LIKEPROC)">
					<text class="ipclass"
						x="{$procX_}" 
						y="{$procY_ - 4}">PROCESSOR</text>		
				</xsl:if>			
				  
				<xsl:if test = "@IS_LIKEPROC = 'TRUE'">
					<text class="ipclass"
						x="{$procX_}" 
						y="{$procY_ - 4}">USER MODULE</text>		
				</xsl:if>			
			
			</xsl:for-each>
		</symbol>
</xsl:template>	


<xsl:template name="Define_Processor">
	<xsl:param name="iProcInst"  select="@INSTANCE"/>
	<xsl:param name="iModType"   select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$iProcInst]/@MODTYPE"/>
<!--	
	<xsl:param name="procType"  select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$procInst]/@PROCTYPE"/>
-->	
	
	<xsl:variable name="label_y_">
		<xsl:value-of select="$BLKD_MOD_LANE_H"/>	
	</xsl:variable>
	
<!--	
	<xsl:message>The proctype is <xsl:value-of select="$procType"/></xsl:message>	
-->
	
	<xsl:variable name="procH_" select="(($BLKD_MOD_LANE_H * 2) + (($BLKD_BIF_H + $BLKD_MOD_BIF_GAP_V) * @BIFS_H) + ($BLKD_MOD_LABEL_H + $BLKD_MOD_BIF_GAP_V))"/>	
	<xsl:variable name="procW_" select="(($BLKD_MOD_LANE_W * 2) + (($BLKD_BIF_W                        * @BIFS_W) + $BLKD_MOD_BIF_GAP_H))"/>	
	
	<xsl:variable name="procColor_">
		<xsl:choose>
			<xsl:when test="contains($iModType,'microblaze')"><xsl:value-of select="$COL_PROC_BG_MB"/></xsl:when>
			<xsl:when test="contains($iModType,'ppc')"><xsl:value-of select="$COL_PROC_BG_PP"/></xsl:when>
			<xsl:otherwise>
				<xsl:value-of select="$COL_PROC_BG_USR"/>	
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
<!--	
	<xsl:message>The proc color is <xsl:value-of select="$procColor"/></xsl:message>	
-->	
	

	<xsl:variable name="procName_">
		<xsl:call-template name="_gen_Stack_SymbolName"> 
			<xsl:with-param name="iHorizIdx" select="@STACK_HORIZ_INDEX"/>
			<xsl:with-param name="iVertiIdx" select="@SHAPE_VERTI_INDEX"/>
		</xsl:call-template>		
	</xsl:variable>	
	
<!--	
	<xsl:message>The proc name is <xsl:value-of select="$procName_"/></xsl:message>	
-->	
	
    <symbol id="{$procName_}">

		<rect x="0"
		      y="0"
			  rx="6" 
			  ry="6" 
		      width = "{$procW_}"
		      height= "{$procH_}"
			  style="fill:{$procColor_}; stroke:{$COL_WHITE}; stroke-width:2"/>		
			  
			  
		<rect x="{ceiling($procW_ div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$BLKD_MOD_LANE_H}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_MOD_LABEL_H}"
			  style="fill:{$COL_WHITE}; stroke:none;"/>		
			  
		<text class="bciptype" 
			  x="{ceiling($procW_ div 2)}"
			  y="{$BLKD_MOD_LANE_H + 8}">
				<xsl:value-of select="$iModType"/>
		</text>
				
		<text class="bciplabel" 
			  x="{ceiling($procW_ div 2)}"
			  y="{$BLKD_MOD_LANE_H + 16}">
				<xsl:value-of select="$iProcInst"/>
	   </text>
	   
	   
	  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$iProcInst]/@GROUP">
	  	
		<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$BLKD_MOD_LANE_H + $BIF_H  + ceiling($BLKD_BIF_H div 3) - 2}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_BIF_H}"
			  style="fill:{$COL_IORING_LT}; stroke:none;"/>		
			  
	
	   	   <text class="ioplblgrp"  x="{ceiling($BLKD_MOD_W div 2)}" y="{$BLKD_MOD_LANE_H + $BIF_H + ceiling($BIF_H div 3) + 12}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE = $iProcInst]/@GROUP"/>
	   		</text>
	   
	  	</xsl:if> 
	   
	   
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iProcInst)]/BUSINTERFACE[(@BIF_X and @BIF_Y)]">
			
			<xsl:variable name="bif_busstd_">
				<xsl:choose>
					<xsl:when test="@BUSSTD">
						<xsl:value-of select="@BUSSTD"/>	
					</xsl:when>
					<xsl:otherwise>
						<xsl:value-of select="'TRS'"/>	
					</xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<xsl:variable name="bif_buscol_">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="$bif_busstd_"/>
				</xsl:call-template>
			</xsl:variable>
		
			
			<xsl:variable name="bif_name_">
				<xsl:choose>
					<xsl:when test="string-length(@NAME) &lt;= 5">
						<xsl:value-of select="@NAME"/>	
					</xsl:when>
					<xsl:otherwise>
						<xsl:value-of select="substring(@NAME,0,5)"/>	
					</xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<xsl:variable name="bif_x_"  select="(( $BLKD_BIF_W * @BIF_X) + ($BLKD_MOD_BIF_GAP_H * @BIF_X) + ($BLKD_MOD_LANE_W * 1))"/>
			<xsl:variable name="bif_y_"  select="((($BLKD_BIF_H + $BLKD_MOD_BIF_GAP_V) * @BIF_Y) + ($BLKD_MOD_LANE_H + $BLKD_MOD_LABEL_H + $BLKD_MOD_BIF_GAP_V))"/>
			
			<xsl:variable name="horz_line_y_" select="($bif_y_ + ceiling($BLKD_BIFC_H div 2))"/>
			
			<xsl:variable name="horz_line_x1_">
				<xsl:choose>
					<xsl:when test="@BIF_X = '0'">0</xsl:when>
					<xsl:otherwise><xsl:value-of select="($BLKD_MOD_W - $BLKD_MOD_LANE_W)"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<xsl:variable name="horz_line_x2_">
				<xsl:choose>
					<xsl:when test="@BIF_X = '0'"><xsl:value-of select="$BLKD_MOD_LANE_W"/></xsl:when>
					<xsl:otherwise><xsl:value-of select="$BLKD_MOD_W + 1"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			
			<line x1="{$horz_line_x1_}" 
			  	  y1="{$horz_line_y_ - 2}"
			      x2="{$horz_line_x2_}" 
			      y2="{$horz_line_y_ - 2}" 
			      style="stroke:{$bif_buscol_};stroke-width:1"/>
			  
			<use  x="{$bif_x_}"   y="{$bif_y_}"  xlink:href="#{$bif_busstd_}_Bif"/>
				
			<text class="biflabel" 
				  x="{$bif_x_ + ceiling($BIF_W div 2)}"
				  y="{$bif_y_ + ceiling($BIF_H div 2) + 3}">
					<xsl:value-of select="$bif_name_"/>
			</text>
			
		</xsl:for-each>
		
		<xsl:variable name="interrupt_cntlr_">
			<xsl:choose>
				<xsl:when test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iProcInst)]/@INTERRUPT_CNTLR">
					<xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iProcInst)]/@INTERRUPT_CNTLR"/>
				</xsl:when>
				<xsl:otherwise>"_no_interrupt_cntlr_"</xsl:otherwise>
			</xsl:choose>
		</xsl:variable>
			
<!--		
		<xsl:message> The intc index should <xsl:value-of select="$interrupt_cntlr_"/></xsl:message>
		<xsl:message> The intc index is <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $interrupt_cntlr_)]/@INTCINDEX"/></xsl:message>
-->		
		<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $interrupt_cntlr_)]/@INTCINDEX">
			
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="iIntcIdx" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $interrupt_cntlr_)]/@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptedProc">
				<xsl:with-param name="iIntr_X"   select="($BLKD_MOD_W - ceiling($BLKD_INTR_W div 2))"/>
				<xsl:with-param name="iIntr_Y"   select="3"/>
				<xsl:with-param name="iIntr_COL" select="$intr_col_"/>
				<xsl:with-param name="iIntr_IDX" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $interrupt_cntlr_)]/@INTCINDEX"/>
			</xsl:call-template>	
		</xsl:if>
		
	</symbol>			  
</xsl:template>

</xsl:stylesheet>
