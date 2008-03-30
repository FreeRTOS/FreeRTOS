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
	======================================================
			BUS INTERFACE DIMENSIONS
	======================================================
-->				
	
<xsl:param name="BIF_H"     select="16"/>				
<xsl:param name="BIF_W"     select="32"/>				
	
<xsl:param name="BIFC_H"    select="24"/>				
<xsl:param name="BIFC_W"    select="24"/>				

<xsl:param name="BIFC_dx"   select="ceiling($BIFC_W div 5)"/>
<xsl:param name="BIFC_dy"   select="ceiling($BIFC_H div 5)"/>
<xsl:param name="BIFC_Hi"   select="($BIFC_H - ($BIFC_dy * 2))"/>	
<xsl:param name="BIFC_Wi"   select="($BIFC_W - ($BIFC_dx * 2))"/>

<xsl:param name="BIF_TYPE_ONEWAY"  select="'OneWay'"/>
	
<!-- +++++++++++++++++++++++++++++++++++++++++++++++++++++ -->
	
	
<!-- 
	======================================================
			BUS DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="BUS_ARROW_W"        select="ceiling($BIFC_W div 3)"/>	
<xsl:variable name="BUS_ARROW_H"        select="ceiling($BIFC_H div 2)"/>
<xsl:variable name="BUS_ARROW_G"        select="ceiling($BIFC_W div 12)"/>
	
<!--
<xsl:variable name="BUS_LANE_W"         select="(ceiling($BIF_W div 2) + $BUS_ARROW_W)"/>	
<xsl:variable name="BUS_LANE_W"         select="($BIFC_W + ceiling($BIFC_W div 2))"/>	
-->	
<xsl:variable name="BUS_LANE_W"         select="($BIF_W + ($MOD_BIF_GAP_H * 2))"/>
<xsl:variable name="SBS_LANE_H"         select="($periMOD_H + ($BIF_H * 2))"/>	
	
<xsl:variable name="P2P_BUS_W"         select="($BUS_ARROW_H - ($BUS_ARROW_G * 2))"/>	
	
<!-- +++++++++++++++++++++++++++++++++++++++++++++++++++++ -->
	
<!-- 
	======================================================
			IO PORT DIMENSIONS
	======================================================
-->				
	
<xsl:param name="IOP_H"   select="16"/>				
<xsl:param name="IOP_W"   select="16"/>				
<xsl:param name="IOP_SPC" select="12"/>				

<xsl:param name="MOD_IO_GAP"   select="8"/>	
<!-- +++++++++++++++++++++++++++++++++++++++++++++++++++++ -->
	
<!-- 
	======================================================
			INTERRUPT NOTATION DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="INTR_W"  select="18"/>
<xsl:variable name="INTR_H"  select="18"/>
	
<!-- +++++++++++++++++++++++++++++++++++++++++++++++++++++ -->
	
	
<!-- 
	======================================================
			MODULE DIMENSIONS
	======================================================
-->				
	
<xsl:variable name="MOD_LABEL_W"   select="(($BIF_W * 2) + $MOD_BIF_GAP_H)"/>
<xsl:variable name="MOD_LABEL_H"   select="(($BIF_H * 2) + ceiling($BIF_H div 3))"/>

<xsl:variable name="MOD_LANE_W"    select="ceiling($BIF_W div 3)"/>
<xsl:variable name="MOD_LANE_H"    select="ceiling($BIF_H div 4)"/>
<xsl:variable name="MOD_EDGE_W"    select="ceiling($MOD_LANE_W div 2)"/>
<xsl:variable name="MOD_SHAPES_G"  select="($BIF_W + $BIF_W)"/>
<xsl:variable name="MOD_BKTLANE_H" select="$BIF_H"/>
<xsl:variable name="MOD_BKTLANE_W" select="$BIF_H"/>
<xsl:variable name="MOD_BUCKET_G"  select="ceiling($BIF_W div 2)"/>
	
<xsl:variable name="MOD_BIF_GAP_H" select="ceiling($BIF_H div 4)"/>				
<xsl:variable name="MOD_BIF_GAP_V" select="ceiling($BIFC_H div 2)"/>				
<!--	
<xsl:variable name="MOD_BIF_GAP_V" select="ceiling($BIF_H div 4)"/>				
-->	

<xsl:variable name="periMOD_W"  select="(               ($BIF_W * 2) + ($MOD_BIF_GAP_H * 1) + ($MOD_LANE_W * 2))"/>
<xsl:variable name="periMOD_H"  select="($MOD_LABEL_H + ($BIF_H * 1) + ($MOD_BIF_GAP_V * 1) + ($MOD_LANE_H * 2))"/>
	
	
<!-- 
	======================================================
			GLOBAL DIAGRAM DIMENSIONS
	======================================================
-->				
<xsl:variable name="BLKD_IORCHAN_H"     select="$BIF_H"/>
<xsl:variable name="BLKD_IORCHAN_W"     select="$BIF_H"/>
<xsl:variable name="BLKD_PRTCHAN_H"     select="($BIF_H * 2) + ceiling($BIF_H div 2)"/>
<xsl:variable name="BLKD_PRTCHAN_W"     select="($BIF_H * 2) + ceiling($BIF_H div 2) + 8"/>
<xsl:variable name="BLKD_DRAWAREA_MIN"  select="(($MOD_BKTLANE_W * 2) + (($periMOD_W * 3) + ($MOD_BUCKET_G * 2)))"/>

<xsl:variable name="BLKD_KEY_W"         select="($BLKD_DRAWAREA_MIN + ceiling($BLKD_DRAWAREA_MIN div 2.5))"/>
<xsl:variable name="BLKD_KEY_H"         select="250"/>

<xsl:variable name="BLKD_SPECS_W"       select="300"/>
<xsl:variable name="BLKD_SPECS_H"       select="100"/>
	
<xsl:variable name="SBS2IP_GAP"         select="$periMOD_H"/>
<xsl:variable name="BKT_MODS_PER_ROW"   select="3"/>
	
<xsl:variable name="IP2UNK_GAP"         select="$periMOD_H"/>
<xsl:variable name="PROC2SBS_GAP"       select="($BIF_H * 2)"/>
<xsl:variable name="IOR2PROC_GAP"       select="$BIF_W"/>
<xsl:variable name="SPECS2KEY_GAP"      select="$BIF_W"/>
<xsl:variable name="BLKD2KEY_GAP"       select="ceiling($BIF_W div 3)"/>
<xsl:variable name="BRIDGE_GAP"         select="($BUS_LANE_W * 4)"/>
	
<xsl:variable name="BLKD_INNER_GAP"     select="ceiling($periMOD_W div 2)"/>
<xsl:variable name="BLKD_INNER_X" 		select="($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W + $BLKD_INNER_GAP)"/>
<xsl:variable name="BLKD_INNER_Y" 		select="($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H + $BLKD_INNER_GAP)"/>
	
</xsl:stylesheet>
