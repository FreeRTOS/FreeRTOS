<?xml version="1.0" standalone="no"?>

<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
                
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
	
<xsl:template name="_calc_Proc_Height">
	<xsl:param name="procInst"  select="_processor_"/>
	
	<xsl:variable name="tot_bifs_h_">
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInst)]/@BIFS_H)">0</xsl:if>
		
		<xsl:if test="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInst)]/@BIFS_H">
			<xsl:variable name="bifs_h_" select="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $procInst)]/@BIFS_H)"/>
			<xsl:value-of select="(($BIF_H + $BIF_GAP) * $bifs_h_)"/>	
		</xsl:if>
	</xsl:variable>	
	
	<xsl:value-of select="(($MOD_LANE_H * 2) + $tot_bifs_h_ + ($MOD_LABEL_H + $BIF_GAP))"/>	
</xsl:template>

<xsl:template name="_calc_Max_Proc_Height">

	<!-- Store the heights in a variable -->	
	<xsl:variable name="proc_heights_">
	
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE)">
			<PROC HEIGHT="0"/>
		</xsl:if>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE">
			<xsl:variable name="procInst_" select="@INSTANCE"/> 
			<xsl:variable name="proc_height_">
				<xsl:call-template name="_calc_Proc_Height">	
					<xsl:with-param name="procInst" select="$procInst_"/>
				</xsl:call-template>	
			</xsl:variable>
			
<!--			
			<xsl:message>Found Proc height as <xsl:value-of select="$proc_height_"/></xsl:message>
-->			
			<PROC HEIGHT="{$proc_height_}"/>
		</xsl:for-each>
	</xsl:variable>
	
	<!-- Return the max of them -->	
<!--	
	<xsl:message>Found Proc ax as <xsl:value-of select="math:max(exsl:node-set($proc_heights_)/PROC/@HEIGHT)"/></xsl:message>
-->	

	<xsl:value-of select="math:max(exsl:node-set($proc_heights_)/PROC/@HEIGHT)"/>
</xsl:template>


<xsl:template name="_calc_Proc_MemoryUnits_Height">
	<xsl:param name="procInst"  select="_processor_"/>
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst) and (@MODCLASS = 'MEMORY_UNIT'))])">0</xsl:if>
	
	<xsl:if test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst) and (@MODCLASS='MEMORY_UNIT'))]">
		
	<xsl:variable name="peri_gap_">
		<xsl:choose>
			<xsl:when test="not(@CSTACK_INDEX)">
				<xsl:value-of select="$BIF_H"/>
			</xsl:when>
			<xsl:otherwise>0</xsl:otherwise>
		</xsl:choose>	
	</xsl:variable>	
			
		
		<!-- Store the all memory unit heights in a variable -->
		<xsl:variable name="memU_heights_">
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst) and (@MODCLASS='MEMORY_UNIT'))]">
<!--				
				<xsl:variable name="unitId_" select="@PSTACK_MODS_Y"/>
-->				
				<xsl:variable name="unitHeight_">
					<xsl:call-template name="_calc_MemoryUnit_Height">	
						<xsl:with-param name="shapeId" select="@SHAPE_ID"/>
					</xsl:call-template>	
				</xsl:variable>
				
				<MEM_UNIT HEIGHT="{$unitHeight_ + $peri_gap_}"/>
			</xsl:for-each>
		</xsl:variable>
		
		<xsl:value-of select="sum(exsl:node-set($memU_heights_)/MEM_UNIT/@HEIGHT)"/>
	</xsl:if>
</xsl:template>
	

<xsl:template name="_calc_Proc_Peripherals_Height">
	<xsl:param name="procInst"  select="_processor_"/>
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst) and not(@MODCLASS = 'MEMORY_UNIT'))])">0</xsl:if>
	
	<xsl:if test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst) and not(@MODCLASS='MEMORY_UNIT'))]">
	
		<xsl:variable name="peri_gap_">
			<xsl:if test="@CSTACK_INDEX">
				<xsl:value-of select="$BIF_H"/>
			</xsl:if>
			<xsl:if test="not(@IS_CSTACK)">0</xsl:if>
		</xsl:variable>
	
		<!-- Store the all peripheral heights in a variable -->
		<xsl:variable name="peri_heights_">
			
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst) and not(@MODCLASS='MEMORY_UNIT'))]">
				<xsl:for-each select="MODULE">
<!--					
					<xsl:message><xsl:value-of select="@INSTANCE"/></xsl:message>		
-->					
					<xsl:variable name="peri_height_">
						<xsl:call-template name="_calc_PeriShape_Height">	
							<xsl:with-param name="shapeInst" select="@INSTANCE"/>
						</xsl:call-template>	
					</xsl:variable>
					<PERI HEIGHT="{$peri_height_ + $peri_gap_}"/>
				</xsl:for-each>		
			</xsl:for-each>
		</xsl:variable>
		
		<xsl:value-of select="sum(exsl:node-set($peri_heights_)/PERI/@HEIGHT)"/>
	</xsl:if>
</xsl:template>
	
	
<xsl:template name="_calc_Space_AbvSbs_Height">
	<xsl:param name="stackToEast"  select="'NONE'"/>
	<xsl:param name="stackToWest"  select="'NONE'"/>
	
	
	<xsl:variable name = "stackAbvSbs_West_H_">
		<xsl:choose>
			<xsl:when test="(($stackToEast = '0')   and     ($stackToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="(($stackToEast = 'NONE') and not($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_AbvSbs_Height">
					<xsl:with-param name="stackIdx"  select="$stackToWest"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:when test="(not($stackToEast = '0') and ($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_AbvSbs_Height">
					<xsl:with-param name="stackIdx"  select="($stackToEast - 1)"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:otherwise>0</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name = "stackAbvSbs_East_H_">
		<xsl:call-template name="_calc_Stack_AbvSbs_Height">
			<xsl:with-param name="stackIdx"  select="$stackToEast"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:variable name="stackAbvSbs_heights_">
		<STACK HEIGHT="{$stackAbvSbs_East_H_}"/>
		<STACK HEIGHT="{$stackAbvSbs_West_H_}"/>
	</xsl:variable>
	
	<xsl:value-of select="math:max(exsl:node-set($stackAbvSbs_heights_)/STACK/@HEIGHT)"/>
</xsl:template>

	
<xsl:template name="_calc_Space_BlwSbs_Height">
	<xsl:param name="stackToEast"  select="'NONE'"/>
	<xsl:param name="stackToWest"  select="'NONE'"/>
		
	<xsl:variable name = "stackBlwSbs_West_H_">
		<xsl:choose>
			<xsl:when test="(($stackToEast = '0')    and    ($stackToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="(($stackToEast = 'NONE') and not($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_BlwSbs_Height">
					<xsl:with-param name="stackIdx"  select="$stackToWest"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:when test="(not($stackToEast = '0') and    ($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_BlwSbs_Height">
					<xsl:with-param name="stackIdx"  select="($stackToEast - 1)"/>
				</xsl:call-template>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>
	
	
	<xsl:variable name = "stackBlwSbs_East_H_">
		<xsl:call-template name="_calc_Stack_BlwSbs_Height">
			<xsl:with-param name="stackIdx"  select="$stackToEast"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:variable name="stackBlwSbs_heights_">
		<STACK HEIGHT="{$stackBlwSbs_East_H_}"/>
		<STACK HEIGHT="{$stackBlwSbs_West_H_}"/>
	</xsl:variable>
	
	<xsl:value-of select="math:max(exsl:node-set($stackBlwSbs_heights_)/STACK/@HEIGHT)"/>
</xsl:template>
	

	
<xsl:template name="_calc_Stack_AbvSbs_Height">
	<xsl:param name="stackIdx"  select="100"/>
<!--	
	<xsl:message>^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^</xsl:message>
-->	
	
	<xsl:if test="(not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@IS_ABVSBS))]) and
				   not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@STACK_HORIZ_INDEX = $stackIdx)]))"><xsl:value-of select="$PROC2SBS_GAP"/></xsl:if>
	
	<xsl:if test="((/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@IS_ABVSBS))]) or
				   (/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@STACK_HORIZ_INDEX = $stackIdx)]))">
		
<!--			
		<xsl:variable name="peri_gap_">
			<xsl:value-of select="$BIF_H"/>
			<xsl:choose>
				<xsl:when test="(@SHAPE_VERTI_INDEX)">
				</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>	
-->			
			
<!--		
		<xsl:message>The gap is <xsl:value-of select="$peri_gap_"/></xsl:message>
		<xsl:message>The gap is <xsl:value-of select="$peri_gap_"/></xsl:message>
		<xsl:message>================================</xsl:message>
		<xsl:message>================================</xsl:message>
		<xsl:message>This is above <xsl:value-of select="@INSTANCE"/></xsl:message>
		<xsl:message><xsl:value-of select="@INSTANCE"/> : <xsl:value-of select="$peri_height_"/></xsl:message>
-->	
	
	
		<!-- Store the all peripheral heights in a variable -->
		<xsl:variable name="peri_heights_">
			
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and not(@MODCLASS = 'MEMORY_UNIT') and (@IS_ABVSBS))]">
				<xsl:for-each select="MODULE">
<!--					
					<xsl:message>This is above <xsl:value-of select="@INSTANCE"/></xsl:message>
-->					
					
					<xsl:variable name="peri_height_">
<!--						
						<xsl:call-template name="_calc_Shape_Height">	
							<xsl:with-param name="shapeId" select="@SHAPE_ID"/>
						</xsl:call-template>	
-->	 
	
						<xsl:call-template name="_calc_PeriShape_Height">	
							<xsl:with-param name="shapeInst" select="@INSTANCE"/>
						</xsl:call-template>	
					</xsl:variable>
					
					<PERI HEIGHT="{$peri_height_ + $BIF_H}"/>
				</xsl:for-each>
			</xsl:for-each>
			
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@MODCLASS = 'MEMORY_UNIT') and (@IS_ABVSBS))]">
			
				<xsl:variable name="memu_height_">
					<xsl:call-template name="_calc_MemoryUnit_Height">	
						<xsl:with-param name="shapeId" select="@SHAPE_ID"/>
					</xsl:call-template>	
				</xsl:variable>
			
<!--				
				<xsl:message>Mem_Unit : <xsl:value-of select="@SHAPE_ID"/> : <xsl:value-of select="$memu_height_ + $peri_gap_"/></xsl:message>
-->				
				<PERI HEIGHT="{$memu_height_ + $BIF_H}"/>
			
			</xsl:for-each>
			
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[((@STACK_HORIZ_INDEX = $stackIdx) and (@IS_ABVSBS))]">
					
				<xsl:variable name="proc_height_">
					<xsl:call-template name="_calc_PeriShape_Height">	
						<xsl:with-param name="shapeInst" select="@INSTANCE"/>
					</xsl:call-template>	
				</xsl:variable>
				
<!--				
		<xsl:message>===================================</xsl:message>
		<xsl:message>Processor : <xsl:value-of select="@INSTANCE"/> : <xsl:value-of select="$peri_height_ + $peri_gap_"/></xsl:message>
				<PERI HEIGHT="{$proc_height_ + $PROC2SBS_GAP }"/>
-->					
				<PERI HEIGHT="{$proc_height_ + $BIF_H}"/>
				
			</xsl:for-each>
		
		</xsl:variable>
		
<!--		
	<xsl:message><xsl:value-of select="@INSTANCE"/> : <xsl:value-of select="$peri_height_ + $peri_gap_"/></xsl:message>
	<xsl:message>================================</xsl:message>
-->
		
<!--		
	<xsl:message>^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^</xsl:message>
-->		
		<xsl:value-of select="sum(exsl:node-set($peri_heights_)/PERI/@HEIGHT)"/>
	</xsl:if>
	
</xsl:template>
	
<xsl:template name="_calc_Stack_BlwSbs_Height">
	<xsl:param name="stackIdx"  select="100"/>
	
<!--	
-->	
			
		<!-- Store the all peripheral heights in a variable -->
		<xsl:variable name="stack_heights_">
			
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@IS_BLWSBS))])">
				<STACKSHAPE HEIGHT="0"/>
			</xsl:if>
			
			<xsl:if test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@IS_BLWSBS))]">
<!--		
		<xsl:message>vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv</xsl:message>
-->	
	
				<xsl:variable name="peri_gap_">
					<xsl:choose>
						<xsl:when test="(@SHAPE_VERTI_INDEX)">
							<xsl:value-of select="$BIF_H"/>
						</xsl:when>
						<xsl:otherwise>0</xsl:otherwise>
					</xsl:choose>	
				</xsl:variable>	
				
				<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and not(@MODCLASS = 'MEMORY_UNIT') and (@IS_BLWSBS))]">
					<xsl:for-each select="MODULE">
<!--					
					<xsl:message>This is below <xsl:value-of select="@INSTANCE"/></xsl:message>
-->	
						<xsl:variable name="peri_height_">
							<xsl:call-template name="_calc_PeriShape_Height">	
								<xsl:with-param name="shapeInst" select="@INSTANCE"/>
							</xsl:call-template>	
						</xsl:variable>
						
						<STACKSHAPE HEIGHT="{$peri_height_ + $peri_gap_}"/>
					</xsl:for-each>
				</xsl:for-each>
		
				<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $stackIdx) and (@MODCLASS = 'MEMORY_UNIT') and (@IS_BLWSBS))]">
			
					<xsl:variable name="memu_height_">
						<xsl:call-template name="_calc_MemoryUnit_Height">	
							<xsl:with-param name="shapeId" select="@SHAPE_ID"/>
						</xsl:call-template>	
					</xsl:variable>
			
					<STACKSHAPE HEIGHT="{$memu_height_ + $peri_gap_}"/>
				
<!--				
				<xsl:message>Mem_Unit : <xsl:value-of select="@SHAPE_ID"/> : <xsl:value-of select="$memu_height_ + $peri_gap_"/></xsl:message>
-->	
			
			</xsl:for-each>
		</xsl:if>
			
		<xsl:variable name="sbsBuckets_H_">
			<xsl:call-template name="_calc_Stack_SbsBuckets_Height">
				<xsl:with-param name="stackIdx" select="$stackIdx"/>
			</xsl:call-template>	
		</xsl:variable>
			
			<STACKSHAPE HEIGHT="{$sbsBuckets_H_}"/>
<!--			
			<xsl:message>Sbs Bucket H : <xsl:value-of select="$sbsBuckets_H_"/></xsl:message>
-->
		</xsl:variable>
		
<!--		
		<xsl:message>vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv</xsl:message>
-->		
		<xsl:value-of select="sum(exsl:node-set($stack_heights_)/STACKSHAPE/@HEIGHT)"/>
	
</xsl:template>
	

<xsl:template name="_calc_Stack_SbsBuckets_Height">
	<xsl:param name="stackIdx"  select="1000"/>
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX = $stackIdx)])">0</xsl:if>
	
	<xsl:if test="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX = $stackIdx)]">
	
		<!-- Store the all buckets heights in a variable -->
		<xsl:variable name="bkt_heights_">
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX = $stackIdx)]">
		
				<xsl:variable name="bkt_height_">
					<xsl:call-template name="_calc_SbsBucket_Height">	
						<xsl:with-param name="bucketId" select="@BUSINDEX"/>
					</xsl:call-template>	
				</xsl:variable>
<!--				
				<xsl:message>Found shared buckets height as <xsl:value-of select="$bkt_height_"/></xsl:message>
-->				
				<BKT HEIGHT="{$bkt_height_ + $BIF_H}"/>
			</xsl:for-each>
		</xsl:variable>
		
		<xsl:value-of select="sum(exsl:node-set($bkt_heights_)/BKT/@HEIGHT)"/>
	</xsl:if>
</xsl:template>

	
<xsl:template name="_calc_Max_Stack_BlwSbs_Height">

	<!-- Store the heights in a variable -->	
	<xsl:variable name="blwSbs_heights_">
		
		<!-- Default, in case there are no modules or ports -->		
		<BLW HEIGHT="0"/>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@EAST &lt; /EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH)]">
	
<!--			
			<xsl:message>Found a space of index <xsl:value-of select="@EAST"/></xsl:message>
-->	
			
			<xsl:variable name="stack_height_">
				<xsl:call-template name="_calc_Stack_BlwSbs_Height">
					<xsl:with-param name="stackIdx"  select="@EAST"/>
				</xsl:call-template>
			</xsl:variable>
			
			
			<BLW HEIGHT="{$stack_height_}"/>
			
		</xsl:for-each>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@WEST = (/EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH -1))]">
			
<!--			
			<xsl:message>Last stack of index <xsl:value-of select="@WEST"/></xsl:message>
-->			
			
			<xsl:variable name="stack_height_">
				<xsl:call-template name="_calc_Stack_BlwSbs_Height">
					<xsl:with-param name="stackIdx"  select="@WEST"/>
				</xsl:call-template>
			</xsl:variable>
			
			
			<BLW HEIGHT="{$stack_height_}"/>
			
		</xsl:for-each>
		
		
	</xsl:variable>
	
<!--	
	<xsl:message>Found Blw Sbs max as <xsl:value-of select="math:max(exsl:node-set($blwSbs_heights_)/BLW/@HEIGHT)"/></xsl:message>
-->	
	<!-- Return the max of them -->	
	<xsl:value-of select="math:max(exsl:node-set($blwSbs_heights_)/BLW/@HEIGHT)"/>
</xsl:template>
	
	
<xsl:template name="_calc_Max_Stack_AbvSbs_Height">

	<!-- Store the heights in a variable -->	
	<xsl:variable name="abvSbs_heights_">
		
		<!-- Default, in case there are no modules or ports -->		
		<ABV HEIGHT="0"/>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@EAST &lt; /EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH)]">
			
<!--			
			<xsl:message>Found a space of index <xsl:value-of select="@EAST"/></xsl:message>
-->	
			
			<xsl:variable name="stack_height_">
				<xsl:call-template name="_calc_Stack_AbvSbs_Height">
					<xsl:with-param name="stackIdx"  select="@EAST"/>
				</xsl:call-template>
			</xsl:variable>
			
<!--			
			<xsl:message>Found stack of width <xsl:value-of select="$stack_width_"/></xsl:message>
			<xsl:message>==============================</xsl:message>
-->			
			
			<ABV HEIGHT="{$stack_height_}"/>
			
		</xsl:for-each>
		
		
	</xsl:variable>
	
<!--	
	<xsl:message>Found Blw Sbs max as <xsl:value-of select="math:max(exsl:node-set($blwSbs_heights_)/BLW/@HEIGHT)"/></xsl:message>
-->	
	<!-- Return the max of them -->	
	<xsl:value-of select="math:max(exsl:node-set($abvSbs_heights_)/ABV/@HEIGHT)"/>
</xsl:template>
	
	
<xsl:template name="_calc_Max_Proc_PerisAbvSbs_Height">
	<xsl:param name="procInst"  select="_processor_"/>
	
	<!-- Store the heights in a variable -->	
	<xsl:variable name="abvSbs_heights_">
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE)">
			<ABV HEIGHT="0"/>
		</xsl:if>
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE">
			<xsl:variable name="procInst_" select="@INSTANCE"/> 
<!--			
			<xsl:message>Found Blw Sbs height as <xsl:value-of select="$blwSbs_"/></xsl:message>
			<ABV HEIGHT="{$pAbvSbs_}"/>
-->			
			
			<xsl:variable name="pAbvSbs_">
				<xsl:call-template name="_calc_Proc_PerisAbvSbs_Height">	
					<xsl:with-param name="procInst" select="$procInst_"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:variable name="memUs_">
				<xsl:call-template name="_calc_Proc_MemoryUnits_Height">	
					<xsl:with-param name="procInst" select="$procInst_"/>
				</xsl:call-template>	
			</xsl:variable>
			
<!--			
			<xsl:message>Found Peris Above height as <xsl:value-of select="$pAbvSbs_"/></xsl:message>
			<xsl:message>Found MemUs Above height as <xsl:value-of select="$memUs_"/></xsl:message>
			<xsl:message>Found PAbv Above height as <xsl:value-of select="($pAbvSbs_ + $memUs_)"/></xsl:message>
-->			
			<ABV HEIGHT="{$pAbvSbs_ + $memUs_}"/>
		</xsl:for-each>
	</xsl:variable>
	
<!--	
	<xsl:message>Found Abv Sbs max as <xsl:value-of select="math:max(exsl:node-set($abvSbs_heights_)/ABV/@HEIGHT)"/></xsl:message>
-->	
	
	<!-- Return the max of them -->	
	<xsl:value-of select="math:max(exsl:node-set($abvSbs_heights_)/ABV/@HEIGHT)"/>
</xsl:template>
	
<xsl:template name="_calc_Max_Proc_SbsBuckets_Height___">

	<!-- Store the heights in a variable -->	
	<xsl:variable name="blwSbs_heights_">
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE)">
			<BLW HEIGHT="0"/>
		</xsl:if>
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE">
			<xsl:variable name="procInst_" select="@INSTANCE"/> 
			<xsl:variable name="sbsBktH_">
				<xsl:call-template name="_calc_Proc_SbsBuckets_Height">	
					<xsl:with-param name="procInst" select="$procInst_"/>
				</xsl:call-template>	
			</xsl:variable>
<!--			
			<xsl:message>Found Blw Sbs height as <xsl:value-of select="$blwSbs_"/></xsl:message>
-->			
			<BKT HEIGHT="{$sbsBktH_}"/>
		</xsl:for-each>
	</xsl:variable>
	
<!--	
	<xsl:message>Found Blw Sbs max as <xsl:value-of select="math:max(exsl:node-set($blwSbs_heights_)/BLW/@HEIGHT)"/></xsl:message>
-->	
	<!-- Return the max of them -->	
	<xsl:value-of select="math:max(exsl:node-set($blwSbs_heights_)/BKT/@HEIGHT)"/>
</xsl:template>
	
<xsl:template name="_calc_Max_SbsBuckets_Height___">
	
	
	<xsl:variable name="bkts_h_">
		
		<xsl:variable name="h_proc_sbsBkts_">
			<xsl:call-template name="_calc_Max_Proc_SbsBuckets_Height"/>	
		</xsl:variable>
		<BKT HEIGHT="{$h_proc_sbsBkts_}"/>
		
	</xsl:variable>	
	
<!--	
	<xsl:variable name="h_perisAbvSbs_">
		<xsl:call-template name="_calc_Proc_PerisAbvSbs_Height">	
			<xsl:with-param name="procInst" select="$procInst"/>
		</xsl:call-template>	
	</xsl:variable>
-->	
	<xsl:value-of select="math:max(exsl:node-set($bkts_h_)/BKT/@HEIGHT)"/>
</xsl:template>
	
	

<xsl:template name="_calc_MultiProc_Stack_Height">
	<xsl:param name="mpstack_blkd_x"  select="100"/>
	
		<xsl:variable name="mpStk_ShpHeights_">
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@HAS_MULTIPROCCONNS) and (@PSTACK_BLKD_X = $mpstack_blkd_x))])">
				<MPSHAPE HEIGHT="0"/>
			</xsl:if>
			
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@HAS_MULTIPROCCONNS) and (@PSTACK_BLKD_X = $mpstack_blkd_x))]">
				<xsl:variable name="shpClass_" select="@MODCLASS"/> 
				<xsl:variable name="shpHeight_">
					<xsl:choose>
						<xsl:when test="$shpClass_ = 'PERIPHERAL'">
<!--							
							<xsl:message>Found Multi Proc Peripheral</xsl:message> 
-->	
							<xsl:call-template name="_calc_PeriShape_Height">	
								<xsl:with-param name="shapeInst" select="MODULE/@INSTANCE"/>
							</xsl:call-template>	
						</xsl:when>
						<xsl:when test="$shpClass_ = 'MEMORY_UNIT'">
<!--							
							<xsl:message>Found Multi Proc Memory Unit</xsl:message> 
-->	
							<xsl:call-template name="_calc_MemoryUnit_Height">	
								<xsl:with-param name="cshpIndex"  select="@CSHAPE_INDEX"/>
							</xsl:call-template>	
						</xsl:when>
						<xsl:otherwise>0</xsl:otherwise>
					</xsl:choose>
				</xsl:variable>
				
<!--				
				<xsl:message>Found <xsl:value-of select="$shpHeight_"/></xsl:message>
-->				
				
				<MPSHAPE HEIGHT="{$shpHeight_}"/>
			</xsl:for-each>
	</xsl:variable>
	
<!--	
	<xsl:message>Found stack of height <xsl:value-of select="sum(exsl:node-set($mpStk_ShpHeights_)/MPSHAPE/@HEIGHT)"/></xsl:message>
-->	
	
	<xsl:value-of select="sum(exsl:node-set($mpStk_ShpHeights_)/MPSHAPE/@HEIGHT)"/>
</xsl:template>

<xsl:template name="_calc_Max_MultiProc_Stack_Height">
	
	<!-- Store the heights in a variable -->	
	
	<xsl:variable name="mpStks_Heights_">
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE)">
			<MPSTK HEIGHT="0"/>
		</xsl:if>
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@PSTACK_BLKD_X)]">
			<xsl:variable name="mpstack_height_">
				<xsl:call-template name="_calc_MultiProc_Stack_Height">
					<xsl:with-param name="mpstack_blkd_x" select="(@PSTACK_BLKD_X + 1)"/>
				</xsl:call-template>
			</xsl:variable>
			
<!--			
			<xsl:message>Found <xsl:value-of select="$mpstack_height_"/></xsl:message>
-->			
			<MPSTK HEIGHT="{$mpstack_height_}"/>
		</xsl:for-each>
		
	</xsl:variable>

		<!-- Return the max of them -->	
	<xsl:value-of select="math:max(exsl:node-set($mpStks_Heights_)/MPSTK/@HEIGHT)"/>
	
</xsl:template>



<xsl:template name="_calc_Stack_Shape_Y">
	
	<xsl:param name="horizIdx"  select="100"/>
	<xsl:param name="vertiIdx"  select="100"/>
	
<!--	
	<xsl:message>Y at H index <xsl:value-of select="$horizIdx"/></xsl:message>
	<xsl:message>Y at V index <xsl:value-of select="$vertiIdx"/></xsl:message>
	<xsl:param name="sbsGap"    select="0"/>
	<xsl:variable name="numSBSs_"     select="count(/EDKSYSTEM/BLKDSHAPES/SBSSHAPES/MODULE)"/>	
	<xsl:variable name="sbs_LANE_H_"    select="($numSBSs_ * $SBS_LANE_H)"/>
	<xsl:variable name="sbsGap_"   select="($PROC2SBS_GAP + $sbs_LANE_H_)"/>
-->	
	
	<xsl:variable name="sbsGap_" select="((count(/EDKSYSTEM/BLKDSHAPES/SBSSHAPES/MODULE) * $SBS_LANE_H) + $PROC2SBS_GAP)"/>	
	
	<xsl:if test="(not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))]) and  
		           not(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(  (@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))])   and
		           not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(     (@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))]))">0</xsl:if>
	
	
	<xsl:if test="((/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))])   or  
		           (/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(  (@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))])   or
		           (/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(     (@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))]))">
		<!-- Store the spaces above this one in a variable -->
		<xsl:variable name="spaces_above_">
		
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX &lt; $vertiIdx))])">
				<SPACE HEIGHT="0"/>
			</xsl:if>
			
			<!-- Store the height of all peripherals and memory units above this one-->
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $horizIdx)  and (@SHAPE_VERTI_INDEX &lt; $vertiIdx))]">
				
				<xsl:if test="not(@MODCLASS='MEMORY_UNIT')">	
					<xsl:variable name="peri_height_">
						<xsl:call-template name="_calc_Shape_Height">	
							<xsl:with-param name="shapeId" select="@SHAPE_ID"/>
						</xsl:call-template>	
					</xsl:variable>
<!--					
					<xsl:message>Found peri height <xsl:value-of select="$peri_height_"/></xsl:message>
-->	
	
					<SPACE HEIGHT="{$peri_height_ + $BIF_H}"/>
				</xsl:if>
				
				<xsl:if test="(@MODCLASS='MEMORY_UNIT')">	
					<xsl:variable name="memu_height_">
						<xsl:call-template name="_calc_MemoryUnit_Height">	
							<xsl:with-param name="shapeId" select="@SHAPE_ID"/>
						</xsl:call-template>	
					</xsl:variable>
<!--					
					<xsl:message>Found unit height <xsl:value-of select="$memu_height_"/></xsl:message>
-->					
					<SPACE HEIGHT="{$memu_height_ + $BIF_H}"/>
				</xsl:if>
				
			</xsl:for-each>
			
			<!-- Store the height of all the processors above this one-->
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[((@STACK_HORIZ_INDEX = $horizIdx)  and (@SHAPE_VERTI_INDEX &lt; $vertiIdx))]">
				<xsl:variable name="proc_height_">
						<xsl:call-template name="_calc_PeriShape_Height">	
							<xsl:with-param name="shapeInst" select="@INSTANCE"/>
						</xsl:call-template>	
				</xsl:variable>
				
				<SPACE HEIGHT="{$proc_height_ + $BIF_H}"/>
			</xsl:for-each>
			
			
			<!-- If its a peripheral that is below the shared busses, or its a shared bus bucket -->
			<!-- add the height of the shared busses and the processor.                           -->
			<xsl:if  test="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))]/@IS_BLWSBS)">
				<SPACE HEIGHT="{$sbsGap_}"/>
			</xsl:if>
			<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[((@STACK_HORIZ_INDEX = $horizIdx) and (@SHAPE_VERTI_INDEX = $vertiIdx))])">
				<SPACE HEIGHT="{$sbsGap_}"/>
			</xsl:if>
			
			<!-- Store the height of all shared bus buckets above this one-->
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[((@STACK_HORIZ_INDEX = $horizIdx)  and (@SHAPE_VERTI_INDEX &lt; $vertiIdx))]">
				<xsl:variable name="bkt_height_">
					<xsl:call-template name="_calc_SbsBucket_Height">
						<xsl:with-param name="bucketId" select="@BUSINDEX"/>
					</xsl:call-template>	
				</xsl:variable>
				
				<SPACE HEIGHT="{$bkt_height_ + $BIF_H}"/>
			</xsl:for-each>
			
		</xsl:variable>
		
		<xsl:value-of select="sum(exsl:node-set($spaces_above_)/SPACE/@HEIGHT)"/>
	</xsl:if>
	
</xsl:template>
	
	
<xsl:template name="_calc_Max_BusConnLane_BifY">
	
	<xsl:param name="busname" select="'_busname_'"/>
	
	<!-- Store the heights in a variable -->	
	<xsl:variable name="busConnYs_">
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/BUSCONNS/BUSCONNLANE/BUSCONN)">
			<BUSCONNY HEIGHT="0"/>
		</xsl:if>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/BUSCONNS/BUSCONNLANE[(@BUSNAME = $busname)]/BUSCONN">
			
			<xsl:variable name="peri_cstk_y_">
				<xsl:call-template name="_calc_CStackShapesAbv_Height">
					<xsl:with-param name="cstackIndex"  select="../@CSTACK_INDEX"/>
					<xsl:with-param name="cstackModY"   select="@CSTACK_MODS_Y"/>
				</xsl:call-template>	
			</xsl:variable>	
				
				<xsl:variable name="peri_bif_dy_">
					<xsl:value-of select="(($BIF_H + $BIF_GAP)  * @BIF_Y)"/>
				</xsl:variable>
				
				<xsl:variable name="peri_bc_y_">
					<xsl:value-of select="($MOD_LANE_H + $MOD_LABEL_H + $BIF_GAP + $peri_bif_dy_ + ceiling($BIF_H div 2)) - ceiling($BIFC_H div 2)"/>
				</xsl:variable>
			
<!--			
			<xsl:message>Found a busconn lane</xsl:message>
-->			
			<BUSCONNY HEIGHT="{$peri_cstk_y_ + $peri_bif_dy_ + $peri_bc_y_}"/>
		</xsl:for-each>
		
	</xsl:variable>

		<!-- Return the max of them -->	
	<xsl:value-of select="math:max(exsl:node-set($busConnYs_)/BUSCONNY/@HEIGHT)"/>
	
</xsl:template>
	
	
<xsl:template name="_calc_Min_BusConnLane_BifY">
	
	<xsl:param name="busname" select="'_busname_'"/>
	
	<!-- Store the heights in a variable -->	
	<xsl:variable name="busConnYs_">
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/BUSCONNS/BUSCONNLANE/BUSCONN)">
			<BUSCONNY HEIGHT="0"/>
		</xsl:if>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/BUSCONNS/BUSCONNLANE[(@BUSNAME = $busname)]/BUSCONN">
			
			<xsl:variable name="peri_cstk_y_">
				<xsl:call-template name="_calc_CStackShapesAbv_Height">
					<xsl:with-param name="cstackIndex"  select="../@CSTACK_INDEX"/>
					<xsl:with-param name="cstackModY"   select="@CSTACK_MODS_Y"/>
				</xsl:call-template>	
			</xsl:variable>	
				
				<xsl:variable name="peri_bif_dy_">
					<xsl:value-of select="(($BIF_H + $BIF_GAP)  * @BIF_Y)"/>
				</xsl:variable>
				
				<xsl:variable name="peri_bc_y_">
					<xsl:value-of select="($MOD_LANE_H + $MOD_LABEL_H + $BIF_GAP + $peri_bif_dy_ + ceiling($BIF_H div 2)) - ceiling($BIFC_H div 2)"/>
				</xsl:variable>
			
<!--			
			<xsl:message>Found a busconn lane</xsl:message>
-->			
			<BUSCONNY HEIGHT="{$peri_cstk_y_ + $peri_bc_y_}"/>
		</xsl:for-each>
		
	</xsl:variable>

		<!-- Return the min of them -->	
	<xsl:value-of select="math:min(exsl:node-set($busConnYs_)/BUSCONNY/@HEIGHT)"/>
	
</xsl:template>
	
<xsl:template name="_calc_Stack_Height">
	<xsl:param name="stackIdx"  select="100"/>
	
	<xsl:variable name="stack_height_">
		<!-- if this is called with no vert index of a shape 
			 it defaults to the total height of the stack -->
		<xsl:call-template name="_calc_Stack_Shape_Y">
			<xsl:with-param name="horizIdx"  select="$stackIdx"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:value-of select="$stack_height_"/>
</xsl:template>
	
<!--	
-->	
	
	
<xsl:template name="_calc_Stack_Width">
	<xsl:param name="stackIdx"  select="100"/>
	
<!--	
	<xsl:message>=============Stack Idx <xsl:value-of select="$stackIdx"/>====</xsl:message>			
-->	
	<xsl:variable name="shape_widths_">	
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[@STACK_HORIZ_INDEX = $stackIdx])">
			<SHAPE WIDTH="0"/>
		</xsl:if>
			
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@STACK_HORIZ_INDEX = $stackIdx])">
			<SHAPE WIDTH="0"/>
		</xsl:if>
			
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@STACK_HORIZ_INDEX = $stackIdx)]">
<!--			
			<xsl:variable name="proc_w_">
				<xsl:value-of select="$periMOD_W"/>
			</xsl:variable>
			<xsl:message>Found processor of width <xsl:value-of select="$proc_w_"/></xsl:message>
-->	
			<SHAPE WIDTH="{$periMOD_W}"/>
		</xsl:for-each>
			
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@STACK_HORIZ_INDEX = $stackIdx)]">
				
			<xsl:variable name="shpClass_" select="@MODCLASS"/> 
			<xsl:variable name="shape_w_">
				<xsl:choose>
						
						<xsl:when test="$shpClass_ = 'PERIPHERAL'">
							<xsl:value-of select="$periMOD_W"/>
						</xsl:when>
						
						<xsl:when test="$shpClass_ = 'MEMORY_UNIT'">
							<xsl:value-of select="($periMOD_W * @MODS_W)"/>
						</xsl:when>
						
						<xsl:otherwise>0</xsl:otherwise>
						
					</xsl:choose>
				</xsl:variable>
				
<!--		
			<xsl:message>Found shape width <xsl:value-of select="$shape_w_"/></xsl:message>
-->				
				
			<SHAPE WIDTH="{$shape_w_}"/>
		</xsl:for-each>
			
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX = $stackIdx)]">
			<xsl:variable name="bucket_w_">
				  <xsl:value-of select="(($MOD_BKTLANE_W * 2) + (($periMOD_W * @MODS_W) + ($MOD_BUCKET_G * (@MODS_W - 1))))"/>
			</xsl:variable>
			
<!--				
			<xsl:message>Found bucket of width <xsl:value-of select="$bucket_w_"/></xsl:message>
-->				
			<SHAPE WIDTH="{$bucket_w_}"/>
		</xsl:for-each>
			
	</xsl:variable>
	
	<xsl:value-of select="math:max(exsl:node-set($shape_widths_)/SHAPE/@WIDTH)"/>
</xsl:template>
	
	
<xsl:template name="_calc_Stack_X">
	<xsl:param name="stackIdx"  select="0"/>
	
	<!-- Store the stack widths in a variable -->	
	
<!--	
	<xsl:message>Looking for stack indexes less than <xsl:value-of select="$stackIdx"/></xsl:message>
-->	
	
	<xsl:variable name="stackspace_widths_">
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES[(@STACK_HORIZ_INDEX &lt; $stackIdx)])">
			<STACKSPACE WIDTH="0"/>
		</xsl:if>
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES[(@STACK_HORIZ_INDEX &lt; $stackIdx)])">
			<STACKSPACE WIDTH="0"/>
		</xsl:if>
		
		<xsl:if test="not(/EDKSYSTEM/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX &lt; $stackIdx)])">
			<STACKSPACE WIDTH="0"/>
		</xsl:if>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@EAST &lt;= $stackIdx)]">
			
<!--		
			<xsl:message>==============================</xsl:message>
			<xsl:message>Found a space of index <xsl:value-of select="@EAST"/></xsl:message>
-->	
			
			<xsl:variable name="space_width_" select="($BUS_LANE_W * @BUSLANES_W)"/>
<!--			
			<xsl:message>Bus lane space width <xsl:value-of select="@BUSLANES_W"/></xsl:message>
			<xsl:message>Bus lane space is <xsl:value-of select="$space_width_"/></xsl:message>
-->	
			
				<xsl:variable name="stack_width_">
					<xsl:if test="not(@EAST = $stackIdx)">
						<xsl:call-template name="_calc_Stack_Width">
							<xsl:with-param name="stackIdx"  select="@EAST"/>
						</xsl:call-template>
					</xsl:if>
					<xsl:if test="(@EAST = $stackIdx)">0</xsl:if>
				</xsl:variable>
			
<!--			
			<xsl:message>Found stack of width <xsl:value-of select="$stack_width_"/></xsl:message>
			<xsl:message>==============================</xsl:message>
-->			
			
			<STACKSPACE WIDTH="{$stack_width_ + $space_width_}"/>
			
		</xsl:for-each>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(not(@EAST) and (@WEST = ($stackIdx -1)))]">
			<xsl:variable name="space_width_" select="($BUS_LANE_W * @BUSLANES_W)"/>
			
<!--			
			<xsl:message>Found end space of <xsl:value-of select="$space_width_"/></xsl:message>
-->			
			<STACKSPACE WIDTH="{$space_width_}"/>
		</xsl:for-each>
		
		
	</xsl:variable>
	
	<xsl:value-of select="sum(exsl:node-set($stackspace_widths_)/STACKSPACE/@WIDTH)"/>
	
</xsl:template>	
	
<xsl:template name="_calc_Space_Width">
	
	<xsl:param name="stackToWest"  select="'NONE'"/>
	<xsl:param name="stackToEast"  select="'NONE'"/>
	
<!--	
	<xsl:message>Stack to West <xsl:value-of select="$stackToWest"/></xsl:message>
	<xsl:message>Stack to East <xsl:value-of select="$stackToEast"/></xsl:message>
-->	
	
	<xsl:variable name="spaceWidth_">
		<xsl:choose>
			<xsl:when test="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[((@EAST = $stackToEast) or (not($stackToWest = 'NONE') and (@WEST = $stackToWest)))]">
				<xsl:value-of select="((/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[((@EAST = $stackToEast) or (not($stackToWest = 'NONE') and (@WEST = $stackToWest)))]/@BUSLANES_W) * $BUS_LANE_W)"/>
			</xsl:when>	
			<xsl:otherwise>0</xsl:otherwise>	
		</xsl:choose>	
	</xsl:variable>	
	
<!--	
	<xsl:message>Space width <xsl:value-of select="$spaceWidth_"/></xsl:message>
-->	
	
	<xsl:value-of select="$spaceWidth_"/>
</xsl:template>
	
	
	
	
<xsl:template name="_calc_Space_X">
	
	<xsl:param name="stackToWest"  select="'NONE'"/>
	<xsl:param name="stackToEast"  select="'NONE'"/>
	
<!--	
	<xsl:message>Stack East <xsl:value-of select="$stackToEast"/></xsl:message>
	<xsl:message>Stack West <xsl:value-of select="$stackToWest"/></xsl:message>
-->	
	
	<!-- Store the stack widths in a variable -->	
	
<!--	
	<xsl:message>Looking for stack indexes less than <xsl:value-of select="$stackIdx"/></xsl:message>
-->	
	
	<xsl:variable name="stackspace_widths_">
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES[(@STACK_HORIZ_INDEX &lt; $stackToEast)])">
			<STACKSPACE WIDTH="0"/>
		</xsl:if>
		
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES[(@STACK_HORIZ_INDEX &lt; $stackToEast)])">
			<STACKSPACE WIDTH="0"/>
		</xsl:if>
		
		<xsl:if test="not(/EDKSYSTEM/SBSBUCKETS/SBSBUCKET[(@STACK_HORIZ_INDEX &lt; $stackToEast)])">
			<STACKSPACE WIDTH="0"/>
		</xsl:if>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[((@EAST &lt; $stackToEast) or (not($stackToWest = 'NONE') and (@EAST &lt;= $stackToWest)))]">
			
<!--		
			<xsl:message>==============================</xsl:message>
			<xsl:message>Found a space of index <xsl:value-of select="@EAST"/></xsl:message>
-->	
			
			<xsl:variable name="space_width_" select="($BUS_LANE_W * @BUSLANES_W)"/>
<!--			
			<xsl:message>Bus lane space width <xsl:value-of select="@BUSLANES_W"/></xsl:message>
			<xsl:message>Bus lane space is <xsl:value-of select="$space_width_"/></xsl:message>
-->	
				<xsl:variable name="stack_width_">
					<xsl:call-template name="_calc_Stack_Width">
						<xsl:with-param name="stackIdx"  select="@EAST"/>
					</xsl:call-template>
				</xsl:variable>
			
<!--			
			<xsl:message>Found stack of width <xsl:value-of select="$stack_width_"/></xsl:message>
			<xsl:message>==============================</xsl:message>
-->			
			
			<STACKSPACE WIDTH="{$stack_width_ + $space_width_}"/>
		</xsl:for-each>
	</xsl:variable>
	
	<xsl:variable name = "stackToWest_W_">
		<xsl:choose>
			<xsl:when test="(($stackToEast = '0')   and     ($stackToWest = 'NONE'))">0</xsl:when>
			<xsl:when test="(($stackToEast = 'NONE') and not($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_Width">
					<xsl:with-param name="stackIdx"  select="$stackToWest"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:when test="(not($stackToEast = '0') and ($stackToWest = 'NONE'))">
				<xsl:call-template name="_calc_Stack_Width">
					<xsl:with-param name="stackIdx"  select="($stackToEast - 1)"/>
				</xsl:call-template>
			</xsl:when>
			<xsl:otherwise>0</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
<!--	
	<xsl:variable name = "stackToEast_W_">
		<xsl:call-template name="_calc_Stack_Width">
			<xsl:with-param name="stackIdx"  select="$stackToEast"/>
		</xsl:call-template>
	</xsl:variable>
	<xsl:variable name ="extSpaceEast_W_" select="ceiling($stackToEast_W_ div 2)"/>
-->	
	
	<xsl:variable name ="extSpaceWest_W_" select="ceiling($stackToWest_W_ div 2)"/>
	 
	<xsl:value-of select="sum(exsl:node-set($stackspace_widths_)/STACKSPACE/@WIDTH) - $extSpaceWest_W_"/>
</xsl:template>	

</xsl:stylesheet>
