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
   ===========================================================================
			CALCULATE GLOBAL VARIABLES BASED ON BLKDIAGRAM DEF IN INPUT XML	
   ===========================================================================
-->
	
<xsl:variable name="G_Total_StandAloneMpmc_H">
	<xsl:if test="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/CMPLXSHAPES/MPMCSHAPE">
		<xsl:value-of select="($BLKD_MPMC_MOD_H + $BLKD_MPMC2PROC_GAP)"/>	
	</xsl:if>
	<xsl:if test="not($G_ROOT/EDKSYSTEM/BLKDIAGRAM/CMPLXSHAPES/MPMCSHAPE)">0</xsl:if>
</xsl:variable>
	
<xsl:variable name="G_Max_Stack_BlwSbs_H">
	<xsl:call-template name="F_Calc_Max_Stack_BlwSbs_Height"/>
</xsl:variable>

<xsl:variable name="G_Max_Stack_AbvSbs_H">
	<xsl:call-template name="F_Calc_Max_Stack_AbvSbs_Height"/>
</xsl:variable>
	
<xsl:variable name="G_Total_Stacks_W">
	<xsl:call-template name="F_Calc_Stack_X">
		<xsl:with-param name="iStackIdx"    select="($G_ROOT/EDKSYSTEM/BLKDIAGRAM/@STACK_HORIZ_WIDTH)"/>
	</xsl:call-template>
</xsl:variable>
	
<xsl:variable name="G_NumOfSharedBusses"   select="count($G_ROOT/EDKSYSTEM/BLKDIAGRAM/SBSSHAPES/MODULE)"/>
<xsl:variable name="G_Total_SharedBus_H"   select="($G_NumOfSharedBusses * $BLKD_SBS_LANE_H)"/>

<xsl:variable name="G_NumOfBridges"        select="count($G_ROOT/EDKSYSTEM/BLKDIAGRAM/BRIDGESHAPES/MODULE)"/>
<xsl:variable name="G_Total_Bridges_W"     select="(($G_NumOfBridges * ($BLKD_MOD_W + ($BLKD_BUS_LANE_W * 2))) + $BLKD_BRIDGE_GAP)"/>
	
<xsl:variable name="G_Total_DrawArea_CLC"  select="($G_Total_Stacks_W + $G_Total_Bridges_W + ($BLKD_INNER_GAP * 2))"/>
	
<xsl:variable name="G_Total_DrawArea_W">
	<xsl:if test="$G_Total_DrawArea_CLC &gt; ($BLKD_KEY_W + $BLKD_SPECS_W + $BLKD_SPECS2KEY_GAP)">
		<xsl:value-of select="$G_Total_DrawArea_CLC"/>
	</xsl:if>
	<xsl:if test="not($G_Total_DrawArea_CLC &gt; ($BLKD_KEY_W + $BLKD_SPECS2KEY_GAP + $BLKD_SPECS_W))">
		<xsl:value-of select="($BLKD_KEY_W + $BLKD_SPECS_W + $BLKD_SPECS2KEY_GAP)"/>
	</xsl:if>
</xsl:variable>
	
<xsl:variable name="G_IpBucketMods_H">
	<xsl:if test="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/IPBUCKET/@MODS_H"><xsl:value-of select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/IPBUCKET/@MODS_H"/></xsl:if>
	<xsl:if test="not($G_ROOT/EDKSYSTEM/BLKDIAGRAM/IPBUCKET/@MODS_H)">0</xsl:if>
</xsl:variable>
<xsl:variable name="G_Total_IpBucket_H"   select="($G_IpBucketMods_H * ($BLKD_MOD_H + $BLKD_BIF_H))"/>
	
<xsl:variable name="G_Total_UnkBucket_H">
	<xsl:if test="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET">
	
		<xsl:variable name="unkBucketMods_H_">
			<xsl:if test="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET/@MODS_H"><xsl:value-of select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET/@MODS_H"/></xsl:if>
			<xsl:if test="not($G_ROOT/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET/@MODS_H)">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="total_UnkMod_H_"       select="($unkBucketMods_H_ * ($BLKD_MOD_H + $BLKD_BIF_H))"/> 	
		
		<xsl:variable name="unkBucketBifs_H_">
			<xsl:if test="/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET/@BIFS_H"><xsl:value-of select="/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET/@BIFS_H"/></xsl:if>
			<xsl:if test="not($G_ROOT/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET/@BIFS_H)">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="total_UnkBif_H_"       select="($unkBucketBifs_H_ * ($BLKD_MOD_H + $BLKD_BIF_H))"/>
		
		<xsl:value-of select="($total_UnkBif_H_ + $total_UnkMod_H_)"/>	
	</xsl:if>
	
	<xsl:if test="not($G_ROOT/EDKSYSTEM/BLKDIAGRAM/UNKBUCKET)">0</xsl:if>
</xsl:variable>
	
<xsl:variable name="G_SharedBus_Y"    select="($BLKD_INNER_Y + $G_Total_StandAloneMpmc_H + $G_Max_Stack_AbvSbs_H + $BLKD_PROC2SBS_GAP)"/>
	
<!-- ===========================================================================
    Calculate the width of the Block Diagram based on the total number of      
    buslanes and modules in the design. If there are no buslanes or modules,
	a default width, just wide enough to display the KEY and SPECS is used
   =========================================================================== -->
<xsl:variable name="G_Total_Blkd_W"  select="($G_Total_DrawArea_W + (($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W)* 2))"/>
<xsl:variable name="G_Total_Diag_W"  select="$G_Total_Blkd_W"/>
	
<!-- =========================================================================== -->
<!-- Calculate the height of the Block Diagram based on the total number of      -->
<!-- buslanes and modules in the design. Take into account special shapes such   -->
<!-- as MultiProc shapes.													     -->
<!-- =========================================================================== -->
	
	
<xsl:variable name="G_Total_DrawArea_H"  select="($G_Total_StandAloneMpmc_H + $G_Max_Stack_AbvSbs_H + $BLKD_PROC2SBS_GAP + $G_Total_SharedBus_H + $G_Max_Stack_BlwSbs_H + $BLKD_SBS2IP_GAP + $G_Total_IpBucket_H + $BLKD_IP2UNK_GAP + $G_Total_UnkBucket_H + ($BLKD_INNER_GAP * 2))"/>
<xsl:variable name="G_Total_Blkd_H"      select="($G_Total_DrawArea_H + (($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H)* 2))"/>
	
<xsl:variable name="G_Total_Diag_H">
	<xsl:if test="($IN_TESTMODE = 'TRUE')">
		<xsl:message>Generating Blkdiagram in TestMode </xsl:message>
       <xsl:value-of select="$G_Total_Blkd_H"/>
	</xsl:if>
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
       <xsl:value-of select="($G_Total_Blkd_H + $BLKD_DRAWAREA2KEY_GAP + $BLKD_KEY_H)"/>
	</xsl:if>
</xsl:variable>			

</xsl:stylesheet>
