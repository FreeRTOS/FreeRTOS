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
			<xsl:with-param name="stackIdx"  select="@EAST"/>
		</xsl:call-template>
		
	</xsl:for-each>	
</xsl:template>
	
	
<xsl:template name="Define_Stack"> 
	<xsl:param name="stackIdx"  select="100"/>
	
	<!-- Define the stack's peripheral shapes-->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and not(@MODCLASS = 'MEMORY_UNIT'))]"> 
			
		<xsl:for-each select="MODULE">
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$modInst_)]/@MODTYPE"/>
			<xsl:call-template name="Define_Peripheral"> 
				<xsl:with-param name="modInst"    select="$modInst_"/>
				<xsl:with-param name="modType"    select="$modType_"/>
				<xsl:with-param name="shapeId"    select="../@SHAPE_ID"/>
				<xsl:with-param name="horizIdx"   select="../@STACK_HORIZ_INDEX"/>
				<xsl:with-param name="vertiIdx"   select="../@SHAPE_VERTI_INDEX"/>
			</xsl:call-template>		
		</xsl:for-each>	
		
	</xsl:for-each>
	
	<!-- Define the stack's memory shapes-->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@MODCLASS='MEMORY_UNIT'))]">
		<xsl:call-template name="Define_MemoryUnit"> 
			<xsl:with-param name="shapeId"  select="@SHAPE_ID"/>
		</xsl:call-template>
	</xsl:for-each>
	
	
	<!-- Define the stack's processors-->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE and @BIFS_W and @BIFS_H and (@STACK_HORIZ_INDEX = $stackIdx)]">	
		<xsl:call-template name="Define_Processor"/>		
	</xsl:for-each>	
		
	<!-- Make an inventory of all the things in this processor's stack -->
	<xsl:variable name="pstackW_">
		<xsl:call-template name="_calc_Stack_Width"> 
			<xsl:with-param name="stackIdx"  select="$stackIdx"/>
		</xsl:call-template>		
	</xsl:variable>
		
	<xsl:variable name="pstackH_">
		<xsl:call-template name="_calc_Stack_Height"> 
			<xsl:with-param name="stackIdx"  select="$stackIdx"/>
		</xsl:call-template>		
	</xsl:variable>
	
	<xsl:variable name="procW_"    select="$periMOD_W"/>
	<xsl:variable name="procX_"    select="(ceiling($pstackW_ div 2) - ceiling($procW_ div 2))"/>
	
	<xsl:variable name="numSBSs_"  select="count(/EDKSYSTEM/BLKDSHAPES/SBSSHAPES/MODULE)"/>	
	<xsl:variable name="sbs_H_"    select="($numSBSs_ * $SBS_LANE_H)"/>
	<xsl:variable name="sbsGap_"   select="($PROC2SBS_GAP + $sbs_H_)"/>

	<xsl:variable name="stack_name_">
		<xsl:call-template name="_gen_Stack_Name"> 
			<xsl:with-param name="horizIdx" select="$stackIdx"/>
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
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@STACK_HORIZ_INDEX = $stackIdx)]">
				<xsl:sort select="@STACK_VERTI_INDEX" data-type="number"/>
				
				<xsl:variable name="shapeW_"    select="(@MODS_W * $periMOD_W)"/>
				<xsl:variable name="shapeX_"    select="(ceiling($pstackW_ div 2) - ceiling($shapeW_ div 2))"/>
				<xsl:variable name="shapeY_">
					<xsl:call-template name="_calc_Stack_Shape_Y">
						<xsl:with-param name="horizIdx"  select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="vertiIdx"  select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>
				</xsl:variable>  
				
				<xsl:variable name="stack_SymName_">
					<xsl:call-template name="_gen_Stack_SymbolName"> 
						<xsl:with-param name="horizIdx" select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="vertiIdx" select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>		
				</xsl:variable>
				
<!--				
				<xsl:message>Drawing stack peripheral <xsl:value-of select="$stack_SymName_"/> at <xsl:value-of select="$shapeY_"/></xsl:message>
-->				
				
			 	<use   x="{$shapeX_}"  y="{$shapeY_}"  xlink:href="#{$stack_SymName_}"/> 
			
			</xsl:for-each>
			
			
			<!-- Then draw the slave buckets for the shared busses that this processor is master to -->	
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX = $stackIdx)]">	
				<xsl:sort select="@SHAPE_VERTI_INDEX" data-type="number"/>
			
				<xsl:variable name="bucketW_"   select="(($MOD_BKTLANE_W * 2) + (($periMOD_W * @MODS_W) + ($MOD_BUCKET_G * (@MODS_W - 1))))"/>
				<xsl:variable name="bucketX_"   select="(ceiling($pstackW_ div 2) - ceiling($bucketW_ div 2))"/>
				
				<xsl:variable name="bucketY_">
					<xsl:call-template name="_calc_Stack_Shape_Y">
						<xsl:with-param name="horizIdx"  select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="vertiIdx"  select="@SHAPE_VERTI_INDEX"/>
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
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@STACK_HORIZ_INDEX = $stackIdx)]">
				<xsl:sort select="@SHAPE_VERTI_INDEX" data-type="number"/>
				
				<xsl:variable name="procY_">
					<xsl:call-template name="_calc_Stack_Shape_Y">
						<xsl:with-param name="horizIdx"  select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="vertiIdx"  select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>
				</xsl:variable>  
				
				<xsl:variable name="stack_SymName_">
					<xsl:call-template name="_gen_Stack_SymbolName"> 
						<xsl:with-param name="horizIdx" select="@STACK_HORIZ_INDEX"/>
						<xsl:with-param name="vertiIdx" select="@SHAPE_VERTI_INDEX"/>
					</xsl:call-template>		
				</xsl:variable>
				
			 	<use   x="{$procX_}"  y="{$procY_}"  xlink:href="#{$stack_SymName_}"/> 
<!--				
-->				
				
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
	<xsl:param name="procInst"  select="@INSTANCE"/>
	<xsl:param name="modType"   select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$procInst]/@MODTYPE"/>
<!--	
	<xsl:param name="procType"  select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$procInst]/@PROCTYPE"/>
-->	
	
	<xsl:variable name="label_y_">
		<xsl:value-of select="$MOD_LANE_H"/>	
	</xsl:variable>
	
<!--	
	<xsl:message>The proctype is <xsl:value-of select="$procType"/></xsl:message>	
-->
	
	<xsl:variable name="procH_" select="(($MOD_LANE_H * 2) + (($BIF_H + $MOD_BIF_GAP_V) * @BIFS_H) + ($MOD_LABEL_H + $MOD_BIF_GAP_V))"/>	
	<xsl:variable name="procW_" select="(($MOD_LANE_W * 2) + (($BIF_W                   * @BIFS_W) + $MOD_BIF_GAP_H))"/>	
	
	<xsl:variable name="procColor">
		<xsl:choose>
			<xsl:when test="contains($modType,'microblaze')"><xsl:value-of select="$COL_PROC_BG_MB"/></xsl:when>
			<xsl:when test="contains($modType,'ppc')"><xsl:value-of select="$COL_PROC_BG_PP"/></xsl:when>
<!--			
			<xsl:when test="$procType = 'MICROBLAZE'"><xsl:value-of select="$COL_PROC_BG_MB"/></xsl:when>
			<xsl:when test="$procType = 'POWERPC'"><xsl:value-of select="$COL_PROC_BG_PP"/></xsl:when>
-->	
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
			<xsl:with-param name="horizIdx" select="@STACK_HORIZ_INDEX"/>
			<xsl:with-param name="vertiIdx" select="@SHAPE_VERTI_INDEX"/>
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
			  style="fill:{$procColor}; stroke:{$COL_WHITE}; stroke-width:2"/>		
			  
			  
		<rect x="{ceiling($procW_ div 2) - ceiling($MOD_LABEL_W div 2)}"
		      y="{$MOD_LANE_H}"
			  rx="3" 
			  ry="3" 
		      width= "{$MOD_LABEL_W}"
		      height="{$MOD_LABEL_H}"
			  style="fill:{$COL_WHITE}; stroke:none;"/>		
			  
		<text class="bciptype" 
			  x="{ceiling($procW_ div 2)}"
			  y="{$MOD_LANE_H + 8}">
				<xsl:value-of select="$modType"/>
		</text>
				
		<text class="bciplabel" 
			  x="{ceiling($procW_ div 2)}"
			  y="{$MOD_LANE_H + 16}">
				<xsl:value-of select="$procInst"/>
	   </text>
	   
	   
	  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$procInst]/@GROUP">
	  	
		<rect x="{ceiling($periMOD_W div 2) - ceiling($MOD_LABEL_W div 2)}"
		      y="{$MOD_LANE_H + $BIF_H + ceiling($BIF_H div 3) - 2}"
			  rx="3" 
			  ry="3" 
		      width= "{$MOD_LABEL_W}"
		      height="{$BIF_H}"
			  style="fill:{$COL_IORING_LT}; stroke:none;"/>		
			  
	
	   	   <text class="ioplblgrp"  x="{ceiling($periMOD_W div 2)}" y="{$MOD_LANE_H + $BIF_H + ceiling($BIF_H div 3) + 12}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$procInst]/@GROUP"/>
	   		</text>
	   
	  	</xsl:if> 
	   
	   
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $procInst)]/BUSINTERFACE[(@BIF_X and @BIF_Y)]">
			
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
					<xsl:with-param name="busType" select="$bif_busstd_"/>
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
			
			<xsl:variable name="bif_x_"  select="(($BIF_W * @BIF_X) + ($MOD_BIF_GAP_H * @BIF_X) + ($MOD_LANE_W * 1))"/>
			<xsl:variable name="bif_y_"  select="((($BIF_H + $MOD_BIF_GAP_V) * @BIF_Y) + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
			
			<xsl:variable name="horz_line_y_" select="($bif_y_ + ceiling($BIFC_H div 2))"/>
			
			<xsl:variable name="horz_line_x1_">
				<xsl:choose>
					<xsl:when test="@BIF_X = '0'">0</xsl:when>
					<xsl:otherwise><xsl:value-of select="($periMOD_W - $MOD_LANE_W)"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<xsl:variable name="horz_line_x2_">
				<xsl:choose>
					<xsl:when test="@BIF_X = '0'"><xsl:value-of select="$MOD_LANE_W"/></xsl:when>
					<xsl:otherwise><xsl:value-of select="$periMOD_W + 1"/></xsl:otherwise>
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
				<xsl:when test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$procInst)]/@INTERRUPT_CNTLR">
					<xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$procInst)]/@INTERRUPT_CNTLR"/>
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
					<xsl:with-param name="intcIdx" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $interrupt_cntlr_)]/@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptedProc">
				<xsl:with-param name="intr_col" select="$intr_col_"/>
				<xsl:with-param name="intr_x"   select="($periMOD_W - ceiling($INTR_W div 2))"/>
				<xsl:with-param name="intr_y"   select="3"/>
				<xsl:with-param name="intr_idx" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $interrupt_cntlr_)]/@INTCINDEX"/>
			</xsl:call-template>	
		</xsl:if>
		
	</symbol>			  
</xsl:template>

</xsl:stylesheet>
