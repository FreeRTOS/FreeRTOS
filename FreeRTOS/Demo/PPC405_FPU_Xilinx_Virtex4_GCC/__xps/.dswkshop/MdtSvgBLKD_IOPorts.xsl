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
<xsl:param name="BLKD_IOP_H"   select="16"/>				
<xsl:param name="BLKD_IOP_W"   select="16"/>				
<xsl:param name="BLKD_IOP_SPC" select="12"/>				
<xsl:param name="MOD_IO_GAP"   select="8"/>				
-->
	

<!-- ======================= DEF BLOCK =============================== -->
<xsl:template name="Define_IOPorts">
	
	<xsl:variable name="key_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
	
		<xsl:variable name="key_lt_col_">
			<xsl:call-template name="BusType2LightColor">
				<xsl:with-param name="iBusType" select="'KEY'"/>
			</xsl:call-template>	
		</xsl:variable>

	 <symbol id="G_IOPort">
		<rect  
			x="0"  
			y="0" 
			width= "{$BLKD_IOP_W}" 
			height="{$BLKD_IOP_H}" style="fill:{$COL_IORING_LT}; stroke:{$COL_IORING}; stroke-width:1"/> 
			
		<path class="ioport"
			  d="M   0,0
				 L   {$BLKD_IOP_W},{ceiling($BLKD_IOP_H div 2)}
				 L   0,{$BLKD_IOP_H}
				 Z" style="stroke:none; fill:{$COL_SYSPRT}"/>	
	</symbol>

	 <symbol id="G_BIPort">
		<rect  
			x="0"  
			y="0" 
			width= "{$BLKD_IOP_W}" 
			height="{$BLKD_IOP_H}" style="fill:{$COL_IORING_LT}; stroke:{$COL_IORING}; stroke-width:1"/> 
			
		<path class="btop"
			  d="M 0,{ceiling($BLKD_IOP_H div 2)}
				 {ceiling($BLKD_IOP_W div 2)},0
				 {$BLKD_IOP_W},{ceiling($BLKD_IOP_H div 2)}
				 Z" style="stroke:none; fill:{$COL_SYSPRT}"/>	
				 
		<path class="bbot"
			  d="M 0,{ceiling($BLKD_IOP_H div 2)}
				 {ceiling($BLKD_IOP_W div 2)},{$BLKD_IOP_H}
				 {$BLKD_IOP_W},{ceiling($BLKD_IOP_H div 2)}
				 Z" style="stroke:none; fill:{$COL_SYSPRT}"/>	
				 
	</symbol>

	 <symbol id="KEY_IOPort">
		<rect  
			x="0"  
			y="0" 
			width= "{$BLKD_IOP_W}" 
			height="{$BLKD_IOP_H}" style="fill:{$key_lt_col_}; stroke:none;"/> 
			
		<path class="ioport"
			  d="M   0,0
				 L   {$BLKD_IOP_W},{ceiling($BLKD_IOP_H div 2)}
				 L   0,{$BLKD_IOP_H}
				 Z" style="stroke:none; fill:{$key_col_}"/>	
	</symbol>
	
	 <symbol id="KEY_BIPort">
		<rect  
			x="0"  
			y="0" 
			width= "{$BLKD_IOP_W}" 
			height="{$BLKD_IOP_H}" style="fill:{$key_lt_col_}; stroke:none;"/> 
			
		<path class="btop"
			  d="M 0,{ceiling($BLKD_IOP_H div 2)}
				 {ceiling($BLKD_IOP_W div 2)},0
				 {$BLKD_IOP_W},{ceiling($BLKD_IOP_H div 2)}
				 Z" style="stroke:none; fill:{$key_col_}"/>	
				 
		<path class="bbot"
			  d="M 0,{ceiling($BLKD_IOP_H div 2)}
				 {ceiling($BLKD_IOP_W div 2)},{$BLKD_IOP_H}
				 {$BLKD_IOP_W},{ceiling($BLKD_IOP_H div 2)}
				 Z" style="stroke:none; fill:{$key_col_}"/>
	</symbol>
	
	 <symbol id="KEY_INPort">
		<use   x="0"   y="0"   xlink:href="#KEY_IOPort"/>
		<rect  
			x="{$BLKD_IOP_W}"  
			y="0" 
			width= "{ceiling($BLKD_IOP_W div 2)}" 
			height="{$BLKD_IOP_H}" style="fill:{$COL_SYSPRT}; stroke:none;"/> 
	</symbol>
	
	 <symbol id="KEY_OUTPort">
		<use   x="0"   y="0"   xlink:href="#KEY_IOPort" transform="scale(-1,1) translate({$BLKD_IOP_W * -1},0)"/>
		<rect  
			x="{$BLKD_IOP_W}"  
			y="0" 
			width= "{ceiling($BLKD_IOP_W div 2)}" 
			height="{$BLKD_IOP_H}" style="fill:{$COL_SYSPRT}; stroke:none;"/> 
	</symbol>

	 <symbol id="KEY_INOUTPort">
		<use   x="0"   y="0"   xlink:href="#KEY_BIPort"/>
		<rect  
			x="{$BLKD_IOP_W}"  
			y="0" 
			width= "{ceiling($BLKD_IOP_W div 2)}" 
			height="{$BLKD_IOP_H}" style="fill:{$COL_SYSPRT}; stroke:none;"/> 
	</symbol>


</xsl:template>

<!-- ======================= DRAW BLOCK =============================== -->

<xsl:template name="Draw_IOPorts"> 
	
	<xsl:variable name="ports_count_"    select="count(EXTERNALPORTS/PORT)"/>
	
	<xsl:if test="($ports_count_ &gt; 30)">
		<xsl:call-template name="Draw_IOPorts_4Sides"/> 
	</xsl:if>
	
	<xsl:if test="($ports_count_ &lt;= 30)">
		<xsl:call-template name="Draw_IOPorts_2Sides"/> 
	</xsl:if>
</xsl:template>

<xsl:template name="Draw_IOPorts_2Sides"> 
	
	<xsl:variable name="ports_count_"    select="count(EXTERNALPORTS/PORT)"/>
	<xsl:variable name="ports_per_side_" select="ceiling($ports_count_ div 2)"/>
	
	<xsl:variable name="h_ofs_">
		<xsl:value-of select="$BLKD_PRTCHAN_W + ceiling(($G_total_drawarea_W  - (($ports_per_side_ * $BLKD_IOP_W) + (($ports_per_side_ - 1) * $BLKD_IOP_SPC))) div 2)"/>
	</xsl:variable>
	
	<xsl:variable name="v_ofs_">
		<xsl:value-of select="$BLKD_PRTCHAN_H + ceiling(($G_total_drawarea_H  - (($ports_per_side_ * $BLKD_IOP_H) + (($ports_per_side_ - 1) * $BLKD_IOP_SPC))) div 2)"/>
	</xsl:variable>
	

	<xsl:for-each select="EXTERNALPORTS/PORT">
		<xsl:sort data-type="number" select="@INDEX" order="ascending"/>
		
		<xsl:variable name="poffset_" select="0"/>
		<xsl:variable name="pcount_"  select="$poffset_ + (position() -1)"/>
		
		<xsl:variable name="pdir_">
			<xsl:choose>
				<xsl:when test="(@DIR='I'  or @DIR='IN'  or @DIR='INPUT')">I</xsl:when>
				<xsl:when test="(@DIR='O'  or @DIR='OUT' or @DIR='OUTPUT')">O</xsl:when>
				<xsl:when test="(@DIR='IO' or @DIR='INOUT')">B</xsl:when>
				<xsl:otherwise>I</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="pside_">
			<xsl:choose>
				<xsl:when test="($pcount_ &gt;= ($ports_per_side_ * 0) and ($pcount_ &lt; ($ports_per_side_ * 1)))">W</xsl:when>
				<xsl:when test="($pcount_ &gt;= ($ports_per_side_ * 1) and ($pcount_ &lt; ($ports_per_side_ * 2)))">E</xsl:when>
				<xsl:otherwise>D</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="pdec_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="($ports_per_side_ * 0)"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="($ports_per_side_ * 1)"/></xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="px_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="($BLKD_PRTCHAN_W - $BLKD_IOP_W)"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($h_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_W)) - 2)"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="($BLKD_PRTCHAN_W + ($BLKD_IORCHAN_W * 2) + $G_total_drawarea_W)"/></xsl:when>
				<xsl:when test="($pside_ = 'N')"><xsl:value-of select="($h_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_W)))"/></xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="py_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="($v_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_H)))"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($BLKD_PRTCHAN_H + ($BLKD_IORCHAN_H * 2) + $G_total_drawarea_H)"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="($v_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_H)))"/></xsl:when>
				<xsl:when test="($pside_ = 'N')"><xsl:value-of select="($BLKD_PRTCHAN_H - $BLKD_IOP_H)"/></xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
	
		<xsl:variable name="prot_">
			<xsl:choose>
				<xsl:when test="(($pside_ = 'W') and ($pdir_ = 'I'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'S') and ($pdir_ = 'I'))">-90</xsl:when>
				<xsl:when test="(($pside_ = 'E') and ($pdir_ = 'I'))">180</xsl:when>
				<xsl:when test="(($pside_ = 'N') and ($pdir_ = 'I'))">90</xsl:when>
				
				<xsl:when test="(($pside_ = 'W') and ($pdir_ = 'O'))">180</xsl:when>
				<xsl:when test="(($pside_ = 'S') and ($pdir_ = 'O'))">90</xsl:when>
				<xsl:when test="(($pside_ = 'E') and ($pdir_ = 'O'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'N') and ($pdir_ = 'O'))">-90</xsl:when>
				
				<xsl:when test="(($pside_ = 'W') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'S') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'E') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'N') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		
		<xsl:variable name="txo_">
			<xsl:choose>
				<xsl:when test="($pside_  = 'W')">-10</xsl:when>
				<xsl:when test="($pside_  = 'S')">6</xsl:when>
				 <xsl:when test="($pside_ = 'E')"><xsl:value-of select="(($BLKD_IOP_W * 2) - 4)"/></xsl:when>
				<xsl:when test="($pside_  = 'N')">6</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="tyo_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="ceiling($BLKD_IOP_H div 2) + 6"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($BLKD_IOP_H * 2) + 4"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="ceiling($BLKD_IOP_H div 2) + 6"/></xsl:when>
				<xsl:when test="($pside_ = 'N')">-2</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>

		<xsl:if test="$pdir_ = 'B'">	   
			<use   x="{$px_}"  
			       y="{$py_}"  
				   id="{@NAME}"
			       xlink:href="#G_BIPort" 
			       transform="rotate({$prot_},{$px_ + ceiling($BLKD_IOP_W div 2)},{$py_ + ceiling($BLKD_IOP_H div 2)})"/>
		</xsl:if>
		
		<xsl:if test="(($pside_ = 'S') and not($pdir_ = 'B'))">	   
			<rect  
				x="{$px_}"  
				y="{$py_}" 
				width= "{$BLKD_IOP_W}" 
				height="{$BLKD_IOP_H}" style="stroke:{$COL_IORING}; stroke-width:1"/> 
		</xsl:if>
		
		<xsl:if test="not($pdir_ = 'B')">	   
			<use   x="{$px_}"  
			       y="{$py_}"  
				   id="{@NAME}"
			       xlink:href="#G_IOPort" 
			       transform="rotate({$prot_},{$px_ + ceiling($BLKD_IOP_W div 2)},{$py_ + ceiling($BLKD_IOP_H div 2)})"/>
		</xsl:if>
		
		<text class="iopnumb"
	  		x="{$px_ + $txo_}" 
	  		y="{$py_ + $tyo_}">
			<xsl:value-of select="@INDEX"/><tspan class="iopgrp"><xsl:value-of select="@GROUP"/></tspan>
		</text>
		
	</xsl:for-each>
	
</xsl:template>


<xsl:template name="Draw_IOPorts_4Sides"> 
	
	<xsl:variable name="ports_count_"    select="count(EXTERNALPORTS/PORT)"/>
	<xsl:variable name="ports_per_side_" select="ceiling($ports_count_ div 4)"/>
	
	<xsl:variable name="h_ofs_">
		<xsl:value-of select="$BLKD_PRTCHAN_W + ceiling(($G_total_drawarea_W  - (($ports_per_side_ * $BLKD_IOP_W) + (($ports_per_side_ - 1) * $BLKD_IOP_SPC))) div 2)"/>
	</xsl:variable>
	
	<xsl:variable name="v_ofs_">
		<xsl:value-of select="$BLKD_PRTCHAN_H + ceiling(($G_total_drawarea_H  - (($ports_per_side_ * $BLKD_IOP_H) + (($ports_per_side_ - 1) * $BLKD_IOP_SPC))) div 2)"/>
	</xsl:variable>
	

	<xsl:for-each select="EXTERNALPORTS/PORT">
		<xsl:sort data-type="number" select="@INDEX" order="ascending"/>
		
		<xsl:variable name="poffset_" select="0"/>
		<xsl:variable name="pcount_"  select="$poffset_ + (position() -1)"/>
		
		<xsl:variable name="pdir_">
			<xsl:choose>
				<xsl:when test="(@DIR='I'  or @DIR='IN'  or @DIR='INPUT')">I</xsl:when>
				<xsl:when test="(@DIR='O'  or @DIR='OUT' or @DIR='OUTPUT')">O</xsl:when>
				<xsl:when test="(@DIR='IO' or @DIR='INOUT')">B</xsl:when>
				<xsl:otherwise>I</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="pside_">
			<xsl:choose>
				<xsl:when test="($pcount_ &gt;= ($ports_per_side_ * 0) and ($pcount_ &lt; ($ports_per_side_ * 1)))">W</xsl:when>
				<xsl:when test="($pcount_ &gt;= ($ports_per_side_ * 1) and ($pcount_ &lt; ($ports_per_side_ * 2)))">S</xsl:when>
				<xsl:when test="($pcount_ &gt;= ($ports_per_side_ * 2) and ($pcount_ &lt; ($ports_per_side_ * 3)))">E</xsl:when>
				<xsl:when test="($pcount_ &gt;= ($ports_per_side_ * 3) and ($pcount_ &lt; ($ports_per_side_ * 4)))">N</xsl:when>
				<xsl:otherwise>D</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="pdec_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="($ports_per_side_ * 0)"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($ports_per_side_ * 1)"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="($ports_per_side_ * 2)"/></xsl:when>
				<xsl:when test="($pside_ = 'N')"><xsl:value-of select="($ports_per_side_ * 3)"/></xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="px_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="($BLKD_PRTCHAN_W - $BLKD_IOP_W)"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($h_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_W)) - 2)"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="($BLKD_PRTCHAN_W + ($BLKD_IORCHAN_W * 2) + $G_total_drawarea_W)"/></xsl:when>
				<xsl:when test="($pside_ = 'N')"><xsl:value-of select="($h_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_W)))"/></xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="py_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="($v_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_H)))"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($BLKD_PRTCHAN_H + ($BLKD_IORCHAN_H * 2) + $G_total_drawarea_H)"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="($v_ofs_ + (((position() - 1) - $pdec_) * ($BLKD_IOP_SPC + $BLKD_IOP_H)))"/></xsl:when>
				<xsl:when test="($pside_ = 'N')"><xsl:value-of select="($BLKD_PRTCHAN_H - $BLKD_IOP_H)"/></xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
	
		<xsl:variable name="prot_">
			<xsl:choose>
				<xsl:when test="(($pside_ = 'W') and ($pdir_ = 'I'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'S') and ($pdir_ = 'I'))">-90</xsl:when>
				<xsl:when test="(($pside_ = 'E') and ($pdir_ = 'I'))">180</xsl:when>
				<xsl:when test="(($pside_ = 'N') and ($pdir_ = 'I'))">90</xsl:when>
				
				<xsl:when test="(($pside_ = 'W') and ($pdir_ = 'O'))">180</xsl:when>
				<xsl:when test="(($pside_ = 'S') and ($pdir_ = 'O'))">90</xsl:when>
				<xsl:when test="(($pside_ = 'E') and ($pdir_ = 'O'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'N') and ($pdir_ = 'O'))">-90</xsl:when>
				
				<xsl:when test="(($pside_ = 'W') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'S') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'E') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:when test="(($pside_ = 'N') and ($pdir_ = 'B'))">0</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="txo_">
			<xsl:choose>
				<xsl:when test="($pside_  = 'W')">-14</xsl:when>
				<xsl:when test="($pside_  = 'S')">8</xsl:when>
				 <xsl:when test="($pside_ = 'E')"><xsl:value-of select="(($BLKD_IOP_W * 2) - 4)"/></xsl:when>
				<xsl:when test="($pside_  = 'N')">8</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>
		
		<xsl:variable name="tyo_">
			<xsl:choose>
				<xsl:when test="($pside_ = 'W')"><xsl:value-of select="ceiling($BLKD_IOP_H div 2) + 6"/></xsl:when>
				<xsl:when test="($pside_ = 'S')"><xsl:value-of select="($BLKD_IOP_H * 2) + 4"/></xsl:when>
				<xsl:when test="($pside_ = 'E')"><xsl:value-of select="ceiling($BLKD_IOP_H div 2) + 6"/></xsl:when>
				<xsl:when test="($pside_ = 'N')">-2</xsl:when>
				<xsl:otherwise>0</xsl:otherwise>
			</xsl:choose>	
		</xsl:variable>

		<xsl:if test="$pdir_ = 'B'">	   
			<use   x="{$px_}"
			       y="{$py_}"
				   id="{@NAME}"
			       xlink:href="#G_BIPort" 
			       transform="rotate({$prot_},{$px_ + ceiling($BLKD_IOP_W div 2)},{$py_ + ceiling($BLKD_IOP_H div 2)})"/>
		</xsl:if>
		
		<xsl:if test="(($pside_ = 'S') and not($pdir_ = 'B'))">	   
			<rect  
				x="{$px_}"
				y="{$py_}"
				width= "{$BLKD_IOP_W}"
				height="{$BLKD_IOP_H}" style="stroke:{$COL_IORING}; stroke-width:1"/> 
		</xsl:if>
		
		<xsl:if test="not($pdir_ = 'B')">	   
			<use   x="{$px_}"
			       y="{$py_}"
				   id="{@NAME}"
			       xlink:href="#G_IOPort"
			       transform="rotate({$prot_},{$px_ + ceiling($BLKD_IOP_W div 2)},{$py_ + ceiling($BLKD_IOP_H div 2)})"/>
		</xsl:if>
		
		<text class="iopnumb"
	  		x="{$px_ + $txo_}" 
	  		y="{$py_ + $tyo_}"><xsl:value-of select="@INDEX"/><tspan class="iopgrp"><xsl:value-of select="@GROUP"/></tspan>
		</text>

	</xsl:for-each>
	
</xsl:template>
	
<xsl:template name="Define_ExtPortsTable">
	
<!--	
		<xsl:if test="$oriented_= 'WEST'"><xsl:value-of select="$proc2procX_ - (string-length(@BUSNAME) * 6)"/></xsl:if>	
		<xsl:variable name="max_name_" select="math:max(string-length(/EDKSYSTEM/EXTERNALPORTS/PORT/@NAME))"/>
		<xsl:variable name="max_sgnm_" select="math:max(string-length(/EDKSYSTEM/EXTERNALPORTS/PORT/@SIGNAME))"/>
	
		<xsl:message>MAX NAME <xsl:value-of select="$max_name_"/></xsl:message>
		<xsl:message>MAX SIG  <xsl:value-of select="$max_sgnm_"/></xsl:message>
-->	
	
		<xsl:variable name="ext_ports_">	
			<xsl:if test="not(/EDKSYSTEM/EXTERNALPORTS/PORT)">
				<EXTPORT NAME="__none__" SIGNAME="__none_" NAMELEN="0" SIGLEN="0"/>
			</xsl:if>
			<xsl:if test="/EDKSYSTEM/EXTERNALPORTS/PORT">
				<xsl:for-each select="/EDKSYSTEM/EXTERNALPORTS/PORT">
					<EXTPORT  NAME="{@NAME}" SIGNAME="{@SIGNAME}" NAMELEN="{string-length(@NAME)}" SIGLEN="{string-length(@SIGNAME)}"/>
				</xsl:for-each>
			</xsl:if>
		</xsl:variable>
	
		<xsl:variable name="max_name_" select="math:max(exsl:node-set($ext_ports_)/EXTPORT/@NAMELEN)"/>
		<xsl:variable name="max_sign_" select="math:max(exsl:node-set($ext_ports_)/EXTPORT/@SIGLEN)"/>
	
		<xsl:variable name="h_font_" select="12"/>
		<xsl:variable name="w_font_" select="12"/>
	
		<xsl:variable name="w_num_"    select="($w_font_ * 5)"/>
		<xsl:variable name="w_dir_"    select="($w_font_ * 3)"/>
		<xsl:variable name="w_lsbmsb_" select="($w_font_ * 9)"/>
		<xsl:variable name="w_attr_"   select="($w_font_ * 4)"/>
		<xsl:variable name="w_name_"   select="($w_font_ * $max_name_)"/>
		<xsl:variable name="w_sign_"   select="($w_font_ * $max_sign_)"/>
	
		<xsl:variable name="w_table_" select="($w_num_ + $w_name_ + $w_dir_ + $w_sign_ + $w_attr_)"/>
	
<!--	
		<xsl:message>MAX NAME <xsl:value-of select="$max_name_"/></xsl:message>
		<xsl:message>MAX SIG  <xsl:value-of select="$max_sign_"/></xsl:message>
	
		<xsl:message>W NUM  <xsl:value-of select="$w_num_"/></xsl:message>
		<xsl:message>W DIR  <xsl:value-of select="$w_dir_"/></xsl:message>
		<xsl:message>W NAM  <xsl:value-of select="$w_name_"/></xsl:message>
		<xsl:message>W SIG  <xsl:value-of select="$w_sign_"/></xsl:message>
		<xsl:message>W ATT  <xsl:value-of select="$w_attr_"/></xsl:message>
	
		<xsl:message>W TABLE  <xsl:value-of select="$w_table_"/></xsl:message>
-->	
	
	 <symbol id="BlkDiagram_ExtPortsTable">
		<rect  
			x="0"  
			y="0" 
			width= "{$w_table_}" 
			height="{$h_font_}"  style="fill:{$COL_RED}; stroke:none; stroke-width:1"/> 
	</symbol>	 
	
	
	
</xsl:template>

<!-- ======================= END MAIN BLOCK =========================== -->

</xsl:stylesheet>
