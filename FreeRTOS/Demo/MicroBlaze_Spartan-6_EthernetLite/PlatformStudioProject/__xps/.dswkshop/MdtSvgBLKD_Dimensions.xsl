<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
	   xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
       xmlns:exsl="http://exslt.org/common"
       xmlns:dyn="http://exslt.org/dynamic"
       xmlns:math="http://exslt.org/math"
       xmlns:xlink="http://www.w3.org/1999/xlink"
       extension-element-prefixes="math dyn exsl xlink">
           
           
<!-- 
<xsl:output method="xml" 
			version="1.0" 
			encoding="UTF-8" indent="yes"
	      	doctype-public="-//W3C//DTD SVG Tiny 1.1//EN"
	      	doctype-system="http://www.w3.org/Graphics/SVG/1.1/DTD/svg11-tiny.dtd"/>
-->	

<!-- 
	======================================================
			BUS INTERFACE DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BLKD_BIF_H"     select="16"/>				
<xsl:variable name="BLKD_BIF_W"     select="32"/>				
	
<xsl:variable name="BLKD_BIFC_H"    select="24"/>				
<xsl:variable name="BLKD_BIFC_W"    select="24"/>				

<xsl:variable name="BLKD_BIFC_dx"   select="ceiling($BLKD_BIFC_W div 5)"/>
<xsl:variable name="BLKD_BIFC_dy"   select="ceiling($BLKD_BIFC_H div 5)"/>
<xsl:variable name="BLKD_BIFC_Hi"   select="($BLKD_BIFC_H - ($BLKD_BIFC_dy * 2))"/>	
<xsl:variable name="BLKD_BIFC_Wi"   select="($BLKD_BIFC_W - ($BLKD_BIFC_dx * 2))"/>

<xsl:variable name="BLKD_BIF_TYPE_ONEWAY"  select="'OneWay'"/>
	
<!-- 
	======================================================
			GLOLBAL BUS INTERFACE DIMENSIONS
		(Define for global MdtSVG_BifShapes.xsl which is used across all
	     diagrams to define the shapes of bifs the same across all diagrams)
	======================================================
-->	
	
<xsl:variable name="BIF_H"     select="$BLKD_BIF_H"/>				
<xsl:variable name="BIF_W"     select="$BLKD_BIF_W"/>
	
<xsl:variable name="BIFC_H"    select="$BLKD_BIFC_H"/>
<xsl:variable name="BIFC_W"    select="$BLKD_BIFC_W"/>
	
<xsl:variable name="BIFC_dx"   select="$BLKD_BIFC_dx"/>
<xsl:variable name="BIFC_dy"   select="$BLKD_BIFC_dy"/>
	
<xsl:variable name="BIFC_Hi"   select="$BLKD_BIFC_Hi"/>	
<xsl:variable name="BIFC_Wi"   select="$BLKD_BIFC_Wi"/>


<!-- 
	======================================================
			BUS DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BLKD_P2P_BUS_W"     select="($BLKD_BUS_ARROW_H - ($BLKD_BUS_ARROW_G * 2))"/>	
<xsl:variable name="BLKD_SBS_LANE_H"    select="($BLKD_MOD_H + ($BLKD_BIF_H * 2))"/>	
<xsl:variable name="BLKD_BUS_LANE_W"    select="($BLKD_BIF_W + ($BLKD_MOD_BIF_GAP_H * 2))"/>
<xsl:variable name="BLKD_BUS_ARROW_W"   select="ceiling($BLKD_BIFC_W div 3)"/>	
<xsl:variable name="BLKD_BUS_ARROW_H"   select="ceiling($BLKD_BIFC_H div 2)"/>
<xsl:variable name="BLKD_BUS_ARROW_G"   select="ceiling($BLKD_BIFC_W div 12)"/>
	
	
<!-- 
	======================================================
			IO PORT DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BLKD_IOP_H"   select="16"/>				
<xsl:variable name="BLKD_IOP_W"   select="16"/>				
<xsl:variable name="BLKD_IOP_SPC" select="12"/>				

	
<!-- 
	======================================================
			INTERRUPT NOTATION DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BLKD_INTR_W"  select="18"/>
<xsl:variable name="BLKD_INTR_H"  select="18"/>
	
<!-- 
	======================================================
			MODULE DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BLKD_MOD_IO_GAP"   select="8"/>	
	
<xsl:variable name="BLKD_MOD_W"  select="(                    ($BLKD_BIF_W * 2) + ($BLKD_MOD_BIF_GAP_H * 1) + ($BLKD_MOD_LANE_W * 2))"/>
<xsl:variable name="BLKD_MOD_H"  select="($BLKD_MOD_LABEL_H + ($BLKD_BIF_H * 1) + ($BLKD_MOD_BIF_GAP_V * 1) + ($BLKD_MOD_LANE_H * 2))"/>
	
<xsl:variable name="BLKD_MOD_BIF_GAP_H" select="ceiling($BLKD_BIF_H div 4)"/>				
<xsl:variable name="BLKD_MOD_BIF_GAP_V" select="ceiling($BLKD_BIFC_H div 2)"/>				
	
<xsl:variable name="BLKD_MOD_LABEL_W"   select="(($BLKD_BIF_W * 2) + $BLKD_MOD_BIF_GAP_H)"/>
<xsl:variable name="BLKD_MOD_LABEL_H"   select="(($BLKD_BIF_H * 2) + ceiling($BLKD_BIF_H div 3))"/>
	
<xsl:variable name="BLKD_MOD_LANE_W"    select="ceiling($BLKD_BIF_W div 3)"/>
<xsl:variable name="BLKD_MOD_LANE_H"    select="ceiling($BLKD_BIF_H div 4)"/>
	
<xsl:variable name="BLKD_MOD_EDGE_W"    select="ceiling($BLKD_MOD_LANE_W div 2)"/>
<xsl:variable name="BLKD_MOD_SHAPES_G"  select="($BLKD_BIF_W + $BLKD_BIF_W)"/>
	
<xsl:variable name="BLKD_MOD_BKTLANE_H" select="$BLKD_BIF_H"/>
<xsl:variable name="BLKD_MOD_BKTLANE_W" select="$BLKD_BIF_H"/>
	
<xsl:variable name="BLKD_MOD_BUCKET_G"  select="ceiling($BLKD_BIF_W div 2)"/>
	
<xsl:variable name="BLKD_MPMC_MOD_H"    select="(($BLKD_BIF_H * 1) + ($BLKD_MOD_BIF_GAP_V * 2) + ($BLKD_MOD_LANE_H * 2))"/>
	
	
<!-- 
	======================================================
			GLOBAL DIAGRAM DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BLKD_IORCHAN_H"      select="$BLKD_BIF_H"/>
<xsl:variable name="BLKD_IORCHAN_W"      select="$BLKD_BIF_H"/>
	
<xsl:variable name="BLKD_PRTCHAN_H"      select="($BLKD_BIF_H * 2) + ceiling($BLKD_BIF_H div 2)"/>
<xsl:variable name="BLKD_PRTCHAN_W"      select="($BLKD_BIF_H * 2) + ceiling($BLKD_BIF_H div 2) + 8"/>
	
<xsl:variable name="BLKD_DRAWAREA_MIN_W" select="(($BLKD_MOD_BKTLANE_W * 2) + (($BLKD_MOD_W * 3) + ($BLKD_MOD_BUCKET_G * 2)))"/>
	
<xsl:variable name="BLKD_INNER_X" 		 select="($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W + $BLKD_INNER_GAP)"/>
<xsl:variable name="BLKD_INNER_Y" 		 select="($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H + $BLKD_INNER_GAP)"/>
<xsl:variable name="BLKD_INNER_GAP"      select="ceiling($BLKD_MOD_W div 2)"/>
	
<xsl:variable name="BLKD_SBS2IP_GAP"    select="$BLKD_MOD_H"/>
<xsl:variable name="BLKD_BRIDGE_GAP"    select="($BLKD_BUS_LANE_W * 4)"/>
<xsl:variable name="BLKD_IP2UNK_GAP"    select="$BLKD_MOD_H"/>
<xsl:variable name="BLKD_PROC2SBS_GAP"  select="($BLKD_BIF_H * 2)"/>
<xsl:variable name="BLKD_IOR2PROC_GAP"  select="$BLKD_BIF_W"/>
<xsl:variable name="BLKD_MPMC2PROC_GAP" select="($BLKD_BIF_H * 2)"/>
<xsl:variable name="BLKD_SPECS2KEY_GAP" select="$BLKD_BIF_W"/>
<xsl:variable name="BLKD_DRAWAREA2KEY_GAP"  select="ceiling($BLKD_BIF_W div 3)"/>
	
<xsl:variable name="BLKD_KEY_H"         select="250"/>
<xsl:variable name="BLKD_KEY_W"         select="($BLKD_DRAWAREA_MIN_W + ceiling($BLKD_DRAWAREA_MIN_W div 2.5))"/>
	
	
<xsl:variable name="BLKD_SPECS_H"       select="100"/>
<xsl:variable name="BLKD_SPECS_W"       select="300"/>
	
	
	
<xsl:variable name="BLKD_BKT_MODS_PER_ROW"   select="3"/>
	
<!--		
<xsl:template name="Print_Dimensions">
	<xsl:message>MOD_LABEL_W  : <xsl:value-of select="$MOD_LABEL_W"/></xsl:message>
	<xsl:message>MOD_LABEL_H  : <xsl:value-of select="$MOD_LABEL_H"/></xsl:message>
	
	<xsl:message>MOD_LANE_W   : <xsl:value-of select="$MOD_LANE_W"/></xsl:message>
	<xsl:message>MOD_LANE_H   : <xsl:value-of select="$MOD_LANE_H"/></xsl:message>
	
	<xsl:message>MOD_EDGE_W   : <xsl:value-of select="$MOD_EDGE_W"/></xsl:message>
	<xsl:message>MOD_SHAPES_G : <xsl:value-of select="$MOD_SHAPES_G"/></xsl:message>
	
	<xsl:message>MOD_BKTLANE_W   : <xsl:value-of select="$MOD_BKTLANE_W"/></xsl:message>
	<xsl:message>MOD_BKTLANE_H   : <xsl:value-of select="$MOD_BKTLANE_H"/></xsl:message>
	<xsl:message>MOD_BUCKET_G    : <xsl:value-of select="$MOD_BUCKET_G"/></xsl:message>
	
</xsl:template>		
-->	
	
</xsl:stylesheet>
