<?xml version="1.0" standalone="no"?>
			
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:math="http://exslt.org/math"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink"
           extension-element-prefixes="math">
				
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
			
<!--	
<xsl:variable name="INF_H"   select="$BIF_H       + ceiling($BIF_H div 2)"/>				
<xsl:variable name="INF_W"   select="($BIF_W * 2) + $BIF_GAP"/>
-->	


<!-- ======================= DEF FUNCTIONS =================================== -->

<xsl:template name="Define_FreeCmplxModules">
	
	<xsl:for-each select="BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@IS_PROMOTED and not(@IS_PENALIZED) and not(@STACK_INDEX))]">	
		
		<xsl:variable name="cmplxId_" select="position()"/>
		
		<xsl:if test="@MODCLASS='MEMORY_UNIT'">
			<xsl:call-template name="Define_PeripheralMemory">
				<xsl:with-param name="iPeriId" select="$cmplxId_"/>
			</xsl:call-template>
		</xsl:if>
		
		<xsl:if test="((@MODCLASS='MASTER_SLAVE') or (@MODCLASS = 'MONITOR'))">
			<xsl:variable name="modInst_" select="MODULE/@INSTANCE"/>
			<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$modInst_)]/@MODTYPE"/>
			<xsl:call-template name="Define_Peripheral">
				<xsl:with-param name="iModInst"  select="$modInst_"/>
				<xsl:with-param name="iModType"  select="$modType_"/>
			</xsl:call-template>		
		</xsl:if>
		
	</xsl:for-each>		
</xsl:template>	


<xsl:template name="Define_PenalizedModules">
	
	<xsl:for-each select="BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@IS_PROMOTED and @IS_PENALIZED)]">	
		
		<xsl:variable name="penalId_">unkmodule_<xsl:value-of select="@BKTROW"/>_<xsl:value-of select="@MODS_X"/></xsl:variable>
		
<!--		
		<xsl:message>Drawing penalized module <xsl:value-of select="$penalId_"/></xsl:message>
-->		
		
		<xsl:if test="@MODCLASS='MEMORY_UNIT'">
			<xsl:call-template name="Define_PeripheralMemory">
				<xsl:with-param name="iPeriId" select="$penalId_"/>
			</xsl:call-template>
		</xsl:if>
		
<!--		
		<xsl:if test="((@MODCLASS='MASTER_SLAVE') or (@MODCLASS = 'MONITOR'))">
-->		
			<xsl:variable name="modInst_" select="MODULE/@INSTANCE"/>
			<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInst_)]/@MODTYPE"/>
			<xsl:call-template name="Define_Peripheral">
				<xsl:with-param name="iModInst"  select="$modInst_"/>
				<xsl:with-param name="iModType"  select="$modType_"/>
				<xsl:with-param name="iUnkInst"  select="$penalId_"/>
			</xsl:call-template>		
<!--			
		</xsl:if>
-->		
		
	</xsl:for-each>		
</xsl:template>	


<xsl:template name="Define_IPBucket">
			
	<xsl:for-each select="BLKDSHAPES/IPBUCKET">
		
		<xsl:for-each select="MODULE">	
			
			<xsl:call-template name="Define_IPBucketModule">
				<xsl:with-param name="iIPType"   select="@MODTYPE"/>
				<xsl:with-param name="iIPName"   select="@INSTANCE"/>
			</xsl:call-template>	
			
		</xsl:for-each>		
		
		<symbol id="ipbucket">
			<xsl:variable name="bucket_w_"  select="(($BLKD_MOD_BKTLANE_W * 2) + (($BLKD_MOD_W * @MODS_W) + ($BLKD_MOD_BUCKET_G * (@MODS_W - 1))))"/>
			<xsl:variable name="bucket_h_"  select="(($BLKD_MOD_BKTLANE_H * 2) + (($BLKD_MOD_H * @MODS_H) + ($BLKD_MOD_BUCKET_G * (@MODS_H - 1))))"/>
		
		<rect x="0" 
		      y="0"  
			  rx="4"
			  ry="4"
		      width= "{$bucket_w_}" 
		      height="{$bucket_h_}" 
		      style="stroke-width:2; stroke:{$COL_BLACK}; fill:{$COL_IORING_LT}"/>
				 
			<xsl:variable name="bkt_mods_w_" select="@MODS_W"/>
			
			<xsl:for-each select="MODULE">	
				
				<xsl:variable name="clm_"   select="((     position() - 1)  mod $bkt_mods_w_)"/>
				<xsl:variable name="row_"   select="floor((position() - 1)  div $bkt_mods_w_)"/>
				
				<xsl:variable name="bk_x_"  select="$BLKD_MOD_BKTLANE_W + ($clm_ * ($BLKD_MOD_W + $BLKD_MOD_BUCKET_G))"/>
				<xsl:variable name="bk_y_"  select="$BLKD_MOD_BKTLANE_H + ($row_ * ($BLKD_MOD_H + $BLKD_MOD_BUCKET_G))"/>
				
					 
				<use x="{$bk_x_}"   
					 y="{$bk_y_}" 
					 xlink:href="#ipbktmodule_{@INSTANCE}"/>		  		  
					 
					 
			</xsl:for-each>		 
					 
	</symbol>		
	
</xsl:for-each>	
</xsl:template>	


<xsl:template name="Define_UNKBucket">
			
	<xsl:for-each select="BLKDSHAPES/UNKBUCKET">
	
		<symbol id="unkbucket">
			<xsl:variable name="bucket_w_"  select="(($BLKD_MOD_BKTLANE_W * 2) + (($BLKD_MOD_W * @MODS_W) + ($BLKD_MOD_BUCKET_G * (@MODS_W - 1))))"/>
			<xsl:variable name="bucket_h_"  select="(($BLKD_MOD_BKTLANE_H * 2) + (($BLKD_MOD_H * @MODS_H) + ($BLKD_MOD_BUCKET_G * (@MODS_H - 1))))"/>
		
		<rect x="0" 
		      y="0"  
			  rx="4"
			  ry="4"
		      width= "{$bucket_w_}" 
		      height="{$bucket_h_}" 
		      style="stroke-width:2; stroke:{$COL_BLACK}; fill:{$COL_BG_UNK}"/>
				 
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@IS_PROMOTED and @IS_PENALIZED)]">	
			
			<xsl:variable name="bkt_mods_w_" select="@MODS_W"/>
				
				<xsl:variable name="mod_row_"    select="@BKTROW"/>	
				<xsl:variable name="row_mods_h_" select="/EDKSYSTEM/BLKDSHAPES/UNKBUCKET/BKTROW[(@INDEX = $mod_row_)]/@MODS_H"/>	

<!--				
				<xsl:message>The row module is <xsl:value-of select="@BKTROW"/></xsl:message>
				<xsl:message>The height of the module is <xsl:value-of select="$row_mods_h_"/></xsl:message>
-->				
				
				
				<xsl:variable name="bk_x_"  select="$BLKD_MOD_BKTLANE_W + (@MODS_X * ($BLKD_MOD_W + $BLKD_MOD_BUCKET_G))"/>
				<xsl:variable name="bk_y_"  select="$BLKD_MOD_BKTLANE_H + ($row_mods_h_ * ($BLKD_MOD_H + $BLKD_MOD_BUCKET_G))"/>
				
				<use x="{$bk_x_}"   
					 y="{$bk_y_}" 
					 xlink:href="#symbol_unkmodule_{@BKTROW}_{@MODS_X}"/>		  		  
<!--				 
-->				 

			</xsl:for-each>		 

			
		</symbol>		
		
	</xsl:for-each>	
</xsl:template>	

		
<xsl:template name="Define_SBSBuckets">
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET">	
		
		<xsl:variable name="bus_name_"   select="@BUSNAME"/>
		<xsl:variable name="bus_std_"    select="@BUSSTD"/>
<!--		
		<xsl:variable name="bus_std_"    select="BUSCONNS/BUSCONN/@BUSSTD"/>
-->	
		<xsl:variable name="bus_conn_w_" select="BUSCONNS/@BUSLANE_W"/>
		
		<xsl:variable name="bucket_bg_col_">
			<xsl:call-template name="BusType2LightColor">
				<xsl:with-param name="iBusType" select="$bus_std_"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="bucket_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="iBusType" select="$bus_std_"/>
			</xsl:call-template>
		</xsl:variable>
		
		
		<xsl:for-each select="MODULE">	
			
			<xsl:sort data-type="text" select="@INSTANCE" order="ascending"/>
		
			<xsl:call-template name="Define_SBSBucketModule">
				<xsl:with-param name="iBifType"  select="$bus_std_"/>
				<xsl:with-param name="iIPType"   select="@MODTYPE"/>
				<xsl:with-param name="iIPName"   select="@INSTANCE"/>
			</xsl:call-template>	
			
		</xsl:for-each>		
		
		<symbol id="sbsbucket_{$bus_name_}">
			<xsl:variable name="bucket_w_"  select="(($BLKD_MOD_BKTLANE_W * 2) + (($BLKD_MOD_W * @MODS_W) + ($BLKD_MOD_BUCKET_G * (@MODS_W - 1))))"/>
			<xsl:variable name="bucket_h_"  select="(($BLKD_MOD_BKTLANE_H * 2) + ((($BLKD_MOD_H + $BLKD_BIFC_H) * @MODS_H) + ($BLKD_MOD_BUCKET_G * (@MODS_H - 1))))"/>
			
			<rect x="0"
			      y="0"  
				  rx="4"
				  ry="4"
			      width= "{$bucket_w_}" 
			      height="{$bucket_h_}" 
			      style="stroke-width:2; stroke:{$bucket_col_}; fill:{$bucket_bg_col_}"/>
				 
			<xsl:variable name="bkt_mods_w_" select="@MODS_W"/>
			
			<xsl:for-each select="MODULE">	
				
				<xsl:sort data-type="text" select="@INSTANCE" order="ascending"/>
				
				<xsl:variable name="clm_"   select="((     position() - 1)  mod $bkt_mods_w_)"/>
				<xsl:variable name="row_"   select="floor((position() - 1)  div $bkt_mods_w_)"/>
				
				<xsl:variable name="bk_x_"  select="$BLKD_MOD_BKTLANE_W + ($clm_ * ($BLKD_MOD_W + $BLKD_MOD_BUCKET_G))"/>
				<xsl:variable name="bk_y_"  select="$BLKD_MOD_BKTLANE_H + ($row_ * ($BLKD_MOD_H + $BLKD_BIFC_H + $BLKD_MOD_BUCKET_G))"/>
					 
				<!-- Lay out the module in the bucket -->
				 <use x="{$bk_x_}" y="{$bk_y_}"  xlink:href="#sbsbktmodule_{@INSTANCE}"/>		  
				
				<!-- Add its connection to the piece shared bus -->
				<xsl:variable name="h_bus_y_" select="$bk_y_ + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_P2P_BUS_W div 2)"/>
				
<!--				
				<xsl:variable name="h_bus_x_" select="$bk_x_ - ($BLKD_MOD_BUCKET_G + ceiling($BLKD_MOD_W div 2))"/>
-->	
				<xsl:variable name="h_bus_x_">
					<xsl:choose>
						<xsl:when test="($clm_ = '0')">0</xsl:when>
					
						<xsl:when test="not($clm_ = '0')">
							<xsl:value-of select="$bk_x_ - ($BLKD_MOD_BUCKET_G + ceiling($BLKD_MOD_W div 2))"/>
						</xsl:when>
					</xsl:choose>
				</xsl:variable>
				
<!--				
				<xsl:variable name="h_bus_y_" select="$bk_y_ + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_P2P_BUS_W)"/>
				<xsl:message>h bus x <xsl:value-of select="$h_bus_x_"/></xsl:message>
				<xsl:message>h bus y <xsl:value-of select="$h_bus_y_"/></xsl:message>
-->	
				<xsl:variable name="h_bus_height_" select="$BLKD_P2P_BUS_W"/>
				<xsl:variable name="h_bus_width_"  select="($bk_x_ - $h_bus_x_ + ceiling($BLKD_MOD_W div 2))"/>	
				
				<rect x="{$h_bus_x_}" 
		      		  y="{$h_bus_y_}"  
		      		  width= "{$h_bus_width_}" 
		      		  height="{$BLKD_P2P_BUS_W}" 
		      		  style="fill:{$bucket_col_}"/>
				
			</xsl:for-each>
			
			<xsl:variable name="num_sbsbktmods_" select="count(MODULE)"/>
			<xsl:variable name="num_sbsbktrows_" select="ceiling($num_sbsbktmods_ div $BLKD_BKT_MODS_PER_ROW)"/>
			
			<!-- If there is more than one row, connect the rows with a vertical bar -->		
			<xsl:if test="($num_sbsbktrows_ &gt; 1)">
				
				<xsl:variable name="v_bus_x_"    select="$BLKD_MOD_BKTLANE_W + ($BLKD_MOD_W + $BLKD_MOD_BUCKET_G)"/>
				
				<xsl:variable name="bkt_top_"    select="$BLKD_MOD_BKTLANE_H + (0                      * ($BLKD_MOD_H + $BLKD_BIFC_H + $BLKD_MOD_BUCKET_G))"/>
				<xsl:variable name="bkt_bot_"    select="$BLKD_MOD_BKTLANE_H + (($num_sbsbktrows_ - 1) * ($BLKD_MOD_H + $BLKD_BIFC_H + $BLKD_MOD_BUCKET_G))"/>
				
				<xsl:variable name="v_bus_y_top_" select="$bkt_top_ + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_P2P_BUS_W div 2)"/>
				<xsl:variable name="v_bus_y_bot_" select="$bkt_bot_ + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_P2P_BUS_W div 2)"/>
				
				<xsl:variable name="v_bus_width_"   select="$BLKD_P2P_BUS_W"/>
				<xsl:variable name="v_bus_height_"  select="($v_bus_y_bot_ - $v_bus_y_top_)"/>
				<rect x="0" 
		      		  y="{$v_bus_y_top_}"  
		      		  width= "{$v_bus_width_}" 
		      		  height="{$v_bus_height_}" 
		      		  style="fill:{$bucket_col_}"/>
			</xsl:if>
			
		</symbol>
		
	</xsl:for-each>		
	
	
</xsl:template>	
	
	
<xsl:template name="Define_SBSBucketModule">
	
	<xsl:param name="iBifType"  select="'OPB'"/>
	<xsl:param name="iIPName"   select="'_ipType_'"/>
	<xsl:param name="iIPType"   select="'_ipName_'"/>
	
<!--	
	<xsl:message>The IPType is <xsl:value-of select="$iIPType"/> </xsl:message>
-->	
	<xsl:variable name="bif_y_">
		<xsl:value-of select="$BLKD_MOD_LANE_H + $BLKD_BIFC_H"/>	
	</xsl:variable>

	<xsl:variable name="label_y_">
		<xsl:value-of select="$BLKD_MOD_LANE_H + $BLKD_BIF_H + $BLKD_BIFC_H +  $BLKD_MOD_BIF_GAP_V"/>	
	</xsl:variable>
	
	<xsl:variable name="modBg_Col_">
		<xsl:choose>
			<xsl:when test="$iIPType = 'mpmc'"><xsl:value-of select="$COL_MPMC_BG"/></xsl:when>
			<xsl:otherwise><xsl:value-of select="$COL_BG"/></xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
    <symbol id="sbsbktmodule_{$iIPName}">
		
		<rect x="0"
		      y="{$BLKD_BIFC_H}"
			  rx="6" 
			  ry="6" 
		      width = "{$BLKD_MOD_W}"
		      height= "{$BLKD_MOD_H}"
			  style="fill:{$modBg_Col_}; stroke:{$COL_WHITE}; stroke-width:2"/>		
			  
		<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$label_y_}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_MOD_LABEL_H}"
			  style="fill:{$COL_WHITE}; stroke:none;"/>		
		
	  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/@GROUP">
	  	
			<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      	  y="{$label_y_ + $BLKD_BIF_H + ceiling($BLKD_BIF_H div 3) - 2}"
			      rx="3" 
			      ry="3" 
		      	  width= "{$BLKD_MOD_LABEL_W}"
		          height="{$BLKD_BIF_H}"
			  	  style="fill:{$COL_IORING_LT}; stroke:none;"/>		
			  
	
	   	   <text class="ioplblgrp" 
			  	  x="{ceiling($BLKD_MOD_W div 2)}"
		          y="{$label_y_ + $BLKD_BIF_H + ceiling($BLKD_BIF_H div 3) + 12}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/@GROUP"/>
	   		</text>
	   
	  	</xsl:if> 
	   
		<text class="bciptype" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
			  y="{$label_y_ + 8}">
				<xsl:value-of select="$iIPType"/>
		</text>
				
		<text class="bciplabel" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
			  y="{$label_y_ + 16}">
				<xsl:value-of select="$iIPName"/>
	   </text>
	   
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iIPName)]/BUSINTERFACE[not(@BUSNAME = '__NOC__')]">
			
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
	
		    <xsl:variable name="bif_x_"  select="ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_BIF_W div 2)"/>
			
			<!-- Draw the BIF -->
			<use  x="{$bif_x_}"   y="{$bif_y_}"  xlink:href="#{$bif_busstd_}_Bif"/>
			
<!--			
 			<symbol id="{$bus_type}_busconn_SLAVE">	
-->		 
	 
			<!-- Draw the BIF connection -->
			<use  x="{$bif_x_ + ceiling($BLKD_BIF_W div 2) - ceiling($BLKD_BIFC_W div 2)}"   y="{$bif_y_ - $BLKD_BIFC_H - $BLKD_MOD_LANE_H}"  xlink:href="#{$bif_busstd_}_busconn_{@BIFRANK}"/>
				
			<text class="biflabel" 
				  x="{$bif_x_ + ceiling($BLKD_BIF_W div 2)}"
				  y="{$bif_y_ + ceiling($BLKD_BIF_H div 2) + 3}">
					<xsl:value-of select="$bif_name_"/>
			</text>
			
		</xsl:for-each>
		
		<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/@INTCINDEX">
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="iIntcIdx" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptCntrl">
				<xsl:with-param name="iIntr_X"   select="($BLKD_MOD_W - ceiling($BLKD_INTR_W div 2))"/>
				<xsl:with-param name="iIntr_Y"   select="3 + $BLKD_BIFC_H"/>
				<xsl:with-param name="iIntr_COL" select="$intr_col_"/>
				<xsl:with-param name="iIntr_IDX" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/@INTCINDEX"/>
			</xsl:call-template>	
		</xsl:if>
		
		      
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/INTCCNTLRTRGS/INTCTRG">
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="intcIdx" select="@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptSource">
				<xsl:with-param name="iIntr_X"   select="($BLKD_MOD_W - $BLKD_INTR_W)"/>
				<xsl:with-param name="iIntr_Y"   select="((position() - 1) * (ceiling($BLKD_INTR_H div 2) + 3)) + $BLKD_BIFC_H"/>
				<xsl:with-param name="iIntr_COL" select="$intr_col_"/>
				<xsl:with-param name="iIntr_PRI" select="@PRIORITY"/>
				<xsl:with-param name="iIntr_IDX" select="@INTCINDEX"/>
			</xsl:call-template>	
			
		</xsl:for-each>
		
	</symbol>			  
	
</xsl:template>	

<xsl:template name="Define_IPBucketModule">
	
	<xsl:param name="iIPType"   select="'_ip_type_'"/>
	<xsl:param name="iIPName"   select="'_ip_name_'"/>
	
	<xsl:variable name="bif_y_">
		<xsl:value-of select="$BLKD_MOD_LANE_H"/>	
	</xsl:variable>

	<xsl:variable name="label_y_">
		<xsl:value-of select="(ceiling($BLKD_MOD_H div 2) - ceiling($BLKD_MOD_LABEL_H div 2))"/>	
	</xsl:variable>
	
    <symbol id="ipbktmodule_{$iIPName}">

		<rect x="0"
		      y="0"
			  rx="6" 
			  ry="6" 
		      width = "{$BLKD_MOD_W}"
		      height= "{$BLKD_MOD_H}"
			  style="fill:{$COL_BG}; stroke:{$COL_BLACK}; stroke-width:2"/>		
			  
		<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$label_y_}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_MOD_LABEL_H}"
			  style="fill:{$COL_WHITE}; stroke:none;"/>		
			  
<!--
			  y="{$label_y_ + ceiling($BLKD_MOD_LABEL_H div 2) - 4}"
			  y="{$label_y_ + ceiling($BLKD_MOD_LABEL_H div 2) + 4}"
-->			  

		<text class="bciptype" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
			  y="{$label_y_ + 8}">
				<xsl:value-of select="$iIPType"/>
		</text>
				
		<text class="bciplabel" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
			  y="{$label_y_ + 16}">
				<xsl:value-of select="$iIPName"/>
	   </text>
	   
	  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iIPName)]/@GROUP">
	  	
		<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$label_y_ + $BLKD_BIF_H + ceiling($BLKD_BIF_H div 3) - 2}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_BIF_H}"
			  style="fill:{$COL_IORING_LT}; stroke:none;"/>		
			  
	
	   	   <text class="ioplblgrp" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
		      y="{$label_y_ + $BLKD_BIF_H + ceiling($BLKD_BIF_H div 3) + 12}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$iIPName]/@GROUP"/>
	   		</text>
	   
	  	</xsl:if> 
	  	
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iIPName)]/INTCCNTLRTRGS/INTCTRG">
			
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="iIntcIdx" select="@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptSource">
				<xsl:with-param name="iIntr_X"   select="($BLKD_MOD_W - $BLKD_INTR_W)"/>
				<xsl:with-param name="iIntr_Y"   select="((position() - 1) * (ceiling($BLKD_INTR_H div 2) + 3))"/>
				<xsl:with-param name="iIntr_COL" select="$intr_col_"/>
				<xsl:with-param name="iIntr_PRI" select="@PRIORITY"/>
				<xsl:with-param name="iIntr_IDX" select="@INTCINDEX"/>
			</xsl:call-template>	
			
		</xsl:for-each>
	   
	</symbol>			  
	
</xsl:template>	
	
	
<xsl:template name="Define_Peripheral"> 
<!-- 
	when the module is oriented normal its label goes above the bifs 
    when the module is oriented rot180, (part of a processor memory  
	controller for example) its label goes below the bifs 
-->	

	<xsl:param name="iModVori"    select="'normal'"/>
	<xsl:param name="iModInst"    select="'_instance_'"/>
	<xsl:param name="iModType"    select="'_modtype_'"/>
	<xsl:param name="iUnkInst"    select="'_unknown_'"/>
	<xsl:param name="iHorizIdx"   select="'_unknown_'"/>
	<xsl:param name="iVertiIdx"   select="'_unknown_'"/>
	
<!--	
	<xsl:message>Stack       Y <xsl:value-of select="$cstkMods_Y"/></xsl:message>
	<xsl:message>Stack Index Y <xsl:value-of select="$cstkIndex"/></xsl:message>
-->	
	
	<xsl:variable name="modName_">
		<xsl:choose>
			<xsl:when test="$iUnkInst = '_unknown_'">
				<xsl:value-of select="$iModInst"/>	
			</xsl:when>
			<xsl:otherwise>
				<xsl:value-of select="$iUnkInst"/>	
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="modSymbolName_">
		<xsl:choose>
			<xsl:when test="(not($iHorizIdx = '_unknown_') and not($iVertiIdx = '_unknown_'))">
				<xsl:call-template name="_gen_Stack_SymbolName"> 
					<xsl:with-param name="iHorizIdx"  select="$iHorizIdx"/>
					<xsl:with-param name="iVertiIdx"  select="$iVertiIdx"/>
				</xsl:call-template>		
			</xsl:when>
			<xsl:otherwise>symbol_<xsl:value-of select="$modName_"/></xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="modTypeName_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iModInst)]/@MODTYPE"/>
	
	
<!--	
	<xsl:message>The symbol type of the module is <xsl:value-of select="$modTypeName_"/></xsl:message>
	<xsl:message>The symbol name of the module is <xsl:value-of select="$modSymbolName_"/></xsl:message>
-->	
	
	<xsl:variable name="bifs_h_">	
		<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/MODULE[(@INSTANCE = $iModInst)]/@BIFS_H) and not(/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE[(@INSTANCE = $iModInst)]/@BIFS_H)">0</xsl:if>
	
		<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/MODULE[(@INSTANCE = $iModInst)]/@BIFS_H)">
			<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/MODULE[(@INSTANCE = $iModInst)]/@BIFS_H"/>
		</xsl:if>
	
		<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE[(@INSTANCE = $iModInst)]/@BIFS_H)">
			<xsl:value-of select="/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE[(@INSTANCE = $iModInst)]/@BIFS_H"/>
		</xsl:if>
	</xsl:variable>		
	
	<xsl:variable name="label_y_">
		<xsl:choose>
			<xsl:when test="$iModVori = 'rot180'">
				<xsl:value-of select="($BLKD_MOD_LANE_H + (($BLKD_BIF_H + $BLKD_MOD_BIF_GAP_V) * $bifs_h_))"/>	
			</xsl:when>
			<xsl:otherwise>
				<xsl:value-of select="$BLKD_MOD_LANE_H"/>	
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="bif_dy_">
		<xsl:choose>
			<xsl:when test="$iModVori = 'rot180'">
				<xsl:value-of select="$BLKD_MOD_LANE_H"/>	
			</xsl:when>
			<xsl:otherwise>
				<xsl:value-of select="($BLKD_MOD_LANE_H + $BLKD_MOD_LABEL_H + $BLKD_MOD_BIF_GAP_V)"/>	
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="peri_stroke_col_">
		<xsl:choose>
			<xsl:when test="((@MODCLASS = 'MASTER_SLAVE') or (@MODCLASS = 'MONITOR')) and BUSCONNS/BUSCONN">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="BUSCONNS/BUSCONN/@BUSSTD"/>
				</xsl:call-template>
			</xsl:when>
			
			<xsl:otherwise>
				<xsl:value-of select="$COL_WHITE"/>
			</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="modHeight_">
		<xsl:call-template name="_calc_PeriShape_Height">
			<xsl:with-param name="iShapeInst"  select="$modName_"/>
		</xsl:call-template>	
	</xsl:variable>		
	
    <symbol id="{$modSymbolName_}">
		
		<xsl:if test="$modTypeName_ = 'mpmc'">
		<rect x="0"
		      y="0"
			  rx="6" 
			  ry="6" 
		      width = "{$BLKD_MOD_W}"
		      height= "{$modHeight_}"
			  style="fill:{$COL_MPMC_BG}; stroke:{$peri_stroke_col_}; stroke-width:2"/>		
		</xsl:if>	
		
		<xsl:if test="not($modTypeName_ = 'mpmc')">
		<rect x="0"
		      y="0"
			  rx="6" 
			  ry="6" 
		      width = "{$BLKD_MOD_W}"
		      height= "{$modHeight_}"
			  style="fill:{$COL_BG}; stroke:{$peri_stroke_col_}; stroke-width:2"/>		
		</xsl:if>	
		
					  
		<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$label_y_}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_MOD_LABEL_H}"
			  style="fill:{$COL_WHITE}; stroke:none;"/>		
			  
<!--			  
			  y="{$label_y_ + ceiling($BLKD_MOD_LABEL_H div 2) - 4}">
			  y="{$label_y_ + ceiling($BLKD_MOD_LABEL_H div 2) + 4}">
-->
			  
		<text class="bciptype" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
			  y="{$label_y_ + 8}">
				<xsl:value-of select="$iModType"/>
		</text>
				
		<text class="bciplabel" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
			  y="{$label_y_ + 16}">
				<xsl:value-of select="$iModInst"/>
	   </text>
	   
	  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$iModInst]/@GROUP">
	  	
		<rect x="{ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_MOD_LABEL_W div 2)}"
		      y="{$label_y_ + $BLKD_BIF_H + ceiling($BLKD_BIF_H div 3) - 2}"
			  rx="3" 
			  ry="3" 
		      width= "{$BLKD_MOD_LABEL_W}"
		      height="{$BLKD_BIF_H}"
			  style="fill:{$COL_IORING_LT}; stroke:none;"/>		
			  
	   	   <text class="ioplblgrp" 
			  x="{ceiling($BLKD_MOD_W div 2)}"
		      y="{$label_y_ + $BLKD_BIF_H + ceiling($BLKD_BIF_H div 3) + 12}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$iModInst]/@GROUP"/>
	   		</text>
	   
	  	</xsl:if> 
	   
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$iModInst]/BUSINTERFACE[(@BIF_X and @BIF_Y and not(@BUSNAME = '__NOC__'))]">
			
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
			
			<xsl:variable name="bif_y_">
				<xsl:value-of select="(($BLKD_BIF_H + $BLKD_MOD_BIF_GAP_V)  * @BIF_Y)"/>
			</xsl:variable>
			
			<xsl:variable name="bif_buscol_">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="$bif_busstd_"/>
				</xsl:call-template>
			</xsl:variable>
		
			
			<xsl:variable name="bif_name_">
				<xsl:choose>
					<xsl:when test="not(@NAME)">'UNK'</xsl:when>
					<xsl:when test="string-length(@NAME) &lt;= 5">
						<xsl:value-of select="@NAME"/>	
					</xsl:when>
					<xsl:otherwise>
						<xsl:value-of select="substring(@NAME,0,5)"/>	
					</xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
	
			<xsl:variable name="bif_x_" >
				<xsl:if test="not(@ORIENTED='CENTER')">
					<xsl:value-of select="(($BLKD_BIF_W * @BIF_X) + ($BLKD_MOD_BIF_GAP_H * @BIF_X) + ($BLKD_MOD_LANE_W * 1))"/>
				</xsl:if>
				<xsl:if test="(@ORIENTED='CENTER')">
					<xsl:value-of select="ceiling($BLKD_MOD_W div 2) - ceiling($BLKD_BIF_W div 2)"/>
				</xsl:if>
			</xsl:variable> 
			
			<xsl:if test="not(@IS_INTCONN)">
				<xsl:variable name="horz_line_y_" select="($bif_y_  + $bif_dy_ + ceiling($BLKD_BIFC_H div 2))"/>
			
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
			  
			</xsl:if>
			
			<use  x="{$bif_x_}"   y="{$bif_y_ + $bif_dy_}"  xlink:href="#{$bif_busstd_}_Bif"/>
				
			<text class="biflabel" 
				  x="{$bif_x_  + ceiling($BLKD_BIF_W div 2)}"
				  y="{$bif_y_ + $bif_dy_ + ceiling($BLKD_BIF_H div 2) + 3}">
					<xsl:value-of select="$bif_name_"/>
			</text>
			
		</xsl:for-each>
		
<!--		
		<xsl:if test="@INTCINDEX">
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="intcIdx" select="@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptCntrl">
				<xsl:with-param name="intr_col" select="$intr_col_"/>
				<xsl:with-param name="intr_x"   select="($BLKD_MOD_W - ceiling($BLKD_INTR_W div 2))"/>
				<xsl:with-param name="intr_y"   select="3"/>
				<xsl:with-param name="intr_idx" select="@INTCINDEX"/>
			</xsl:call-template>	
		</xsl:if>
-->		
		<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iModInst)]/@INTCINDEX">
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="iIntcIdx" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iModInst)]/@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptCntrl">
				<xsl:with-param name="iIntr_X"   select="($BLKD_MOD_W - ceiling($BLKD_INTR_W div 2))"/>
				<xsl:with-param name="iIntr_Y"   select="3"/>
				<xsl:with-param name="iIntr_COL" select="$intr_col_"/>
				<xsl:with-param name="iIntr_IDX" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iModInst)]/@INTCINDEX"/>
			</xsl:call-template>	
		</xsl:if>
		
		
		<xsl:for-each select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iModInst)]/INTCCNTLRTRGS/INTCTRG">
			
			<xsl:variable name="intr_col_">
				<xsl:call-template name="intcIdx2Color">
					<xsl:with-param name="iIntcIdx" select="@INTCINDEX"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:call-template name="_draw_InterruptSource">
				<xsl:with-param name="iIntr_X"   select="($BLKD_MOD_W - $BLKD_INTR_W)"/>
				<xsl:with-param name="iIntr_Y"   select="((position() - 1) * (ceiling($BLKD_INTR_H div 2) + 3))"/>
				<xsl:with-param name="iIntr_COL" select="$intr_col_"/>
				<xsl:with-param name="iIntr_PRI" select="@PRIORITY"/>
				<xsl:with-param name="iIntr_IDX" select="@INTCINDEX"/>
			</xsl:call-template>	
			
		</xsl:for-each>
		
	</symbol>			  
</xsl:template>	
	
<xsl:template name="Define_MemoryUnit"> 
	<xsl:param name="iShapeId"  select="1000"/>
	
	<xsl:variable name="horiz_idx_"   select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/@STACK_HORIZ_INDEX"/>
	<xsl:variable name="is_multistk_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/@IS_MULTISTK"/>
	
	<xsl:choose>
		<xsl:when test="(($is_multistk_ = 'TRUE') or (/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@STACK_HORIZ_INDEX = $horiz_idx_)]))">
			<xsl:call-template name="Define_Processor_MemoryUnit"> 
				<xsl:with-param name="iShapeId"  select="$iShapeId"/>
			</xsl:call-template>
		</xsl:when>
		
		<xsl:otherwise>
			<xsl:call-template name="Define_StandAlone_MemoryUnit"> 
				<xsl:with-param name="iShapeId"  select="$iShapeId"/>
			</xsl:call-template>
		</xsl:otherwise>
		
	</xsl:choose>
	
</xsl:template>	
	
	
<xsl:template name="Define_Processor_MemoryUnit"> 
	<xsl:param name="iShapeId"  select="1000"/>
	
<!--	
	<xsl:param name="cstkIndex"    select="'_processor_'"/>
-->	
	
	<xsl:variable name="mods_h_"  select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/@MODS_H"/>
	<xsl:variable name="mods_w_"  select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/@MODS_W"/>
	<xsl:variable name="memW_" select="($BLKD_MOD_W * $mods_w_)"/>
	<xsl:variable name="memH_" select="($BLKD_MOD_H * $mods_h_)"/>
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]">
		
		<!-- first define its symbols as individual modules -->	
		<xsl:for-each select="MODULE[@MODCLASS='MEMORY']">
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$modInst_)]/@MODTYPE"/>
		
			<xsl:call-template name="Define_Peripheral"> 
				<xsl:with-param name="iModVori"  select="'normal'"/>
				<xsl:with-param name="iModInst"  select="$modInst_"/>
				<xsl:with-param name="iModType"  select="$modType_"/>
			</xsl:call-template>		
		</xsl:for-each>	
	
		<xsl:for-each select="MODULE[@MODCLASS='MEMORY_CNTLR']">
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$modInst_)]/@MODTYPE"/>
		
			<xsl:call-template name="Define_Peripheral"> 
				<xsl:with-param name="iModVori"  select="'rot180'"/>
				<xsl:with-param name="iModInst"  select="$modInst_"/>
				<xsl:with-param name="iModType"  select="$modType_"/>
			</xsl:call-template>		
		</xsl:for-each>	
	</xsl:for-each>
	
<!--	
-->	
	
	<xsl:variable name="symbol_name_">
		<xsl:call-template name="_gen_Stack_SymbolName"> 
			<xsl:with-param name="iHorizIdx" select="@STACK_HORIZ_INDEX"/>
			<xsl:with-param name="iVertiIdx" select="@SHAPE_VERTI_INDEX"/>
		</xsl:call-template>		
	</xsl:variable>
	
<!--	
	<xsl:message>The mp stack name is <xsl:value-of select="$mp_stack_name_"/></xsl:message>
-->	
		
    <symbol id="{$symbol_name_}">

		<rect x="0"
		      y="0"
			  rx="6" 
			  ry="6" 
		      width = "{$memW_}"
		      height= "{$memH_}"
			  style="fill:{$COL_BG}; stroke:{$COL_WHITE}; stroke-width:2"/>		
			  
		<!-- Draw the memory block-->		  
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(@MODCLASS = 'MEMORY')]">
			
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 <use  x="{ceiling($memW_ div 2) - ($BLKD_MOD_W div 2)}"  
				   y="0"  
				   xlink:href="#symbol_{$modInst_}"/> 
		</xsl:for-each>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[((@MODCLASS='MEMORY_CNTLR') and (@ORIENTED = 'WEST'))]">
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 <use  x="0"  
				   y="{$BLKD_MOD_H}"  
				   xlink:href="#symbol_{$modInst_}"/> 
		</xsl:for-each>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[((@MODCLASS='MEMORY_CNTLR') and (@ORIENTED = 'EAST'))]">
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 <use  x="{$BLKD_MOD_W}"  
				   y="{$BLKD_MOD_H}"  
				   xlink:href="#symbol_{$modInst_}"/> 
		</xsl:for-each>
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[((@MODCLASS='MEMORY_CNTLR') and (@ORIENTED = 'CENTER'))]">	
			<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 <use  x="{ceiling($memW_ div 2) - ($BLKD_MOD_W div 2)}"  
				   y="{$BLKD_MOD_H}"  
				   xlink:href="#symbol_{$modInst_}"/> 
		</xsl:for-each>
		
	</symbol>			  
	
</xsl:template>	

	
<xsl:template name="Define_StandAlone_MemoryUnit"> 
	
	<xsl:param name="iShapeId" select="0"/>
	
	<xsl:variable name="mods_h_"  select="@MODS_H"/>
	<xsl:variable name="mods_w_"  select="@MODS_W"/>
	
	<xsl:variable name="memc_name_" select="MODULE[not(@MODCLASS = 'MEMORY')]/@INSTANCE"/>
	<xsl:variable name="memc_busstd_" select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE/BUSCONNLANE[(BUSCONN[(@INSTANCE = $memc_name_)])]/@BUSSTD"/>
	
<!--	
	<xsl:variable name="memc_busstd_" select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE/BUSCONNLANE/@BUSSTD"/>
	<xsl:variable name="memc_busstd_" select="/EDKSYSTEM/BCLANESPACES/BCLANESPACE/BUSCONNLANE[(BUSCONN[(@INSTANCE)])]/@BUSSTD"/>
	<xsl:message>Memory cntlr name <xsl:value-of select="$memc_name_"/></xsl:message>
	<xsl:message>Memory cntlr name <xsl:value-of select="$memc_name_"/></xsl:message>
	<xsl:message>Memory cntlr busstd <xsl:value-of select="$memc_busstd_"/></xsl:message>
-->	
	
	<xsl:variable name="peri_col_">
		
		<xsl:choose>
			<xsl:when test="$mods_w_ &gt; 1">
				<xsl:value-of select="$COL_BG"/>
			</xsl:when>
			
			<xsl:when test="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE/BUSCONNLANE[(BUSCONN[(@INSTANCE = $memc_name_)])]/@BUSSTD">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="$memc_busstd_"/>
				</xsl:call-template>
			</xsl:when>
		
			<xsl:otherwise>
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="'TRS'"/>
				</xsl:call-template>
			</xsl:otherwise>
		</xsl:choose>		
		
	</xsl:variable>  
	
	<!-- first define its symbols as individual modules -->	
	<xsl:for-each select="MODULE[(@MODCLASS = 'MEMORY')]">
		<xsl:variable name="modInst_" select="@INSTANCE"/>
		<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$modInst_]/@MODTYPE"/>
		
		<xsl:call-template name="Define_Peripheral"> 
			<xsl:with-param name="iModVori"  select="'rot180'"/>
			<xsl:with-param name="iModInst"  select="$modInst_"/>
			<xsl:with-param name="iModType"  select="$modType_"/>
		</xsl:call-template>		
	</xsl:for-each>	
	
	<xsl:for-each select="MODULE[not(@MODCLASS='MEMORY')]">
		<xsl:variable name="modInst_" select="@INSTANCE"/>
		<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$modInst_]/@MODTYPE"/>
		
<!--		
		<xsl:message>Memory cntlr inst <xsl:value-of select="$modInst_"/></xsl:message>
-->		
		<xsl:call-template name="Define_Peripheral"> 
			<xsl:with-param name="iModVori"  select="'normal'"/>
			<xsl:with-param name="iModInst"  select="$modInst_"/>
			<xsl:with-param name="iModType"  select="$modType_"/>
		</xsl:call-template>		
	</xsl:for-each>	
	
	<xsl:variable name="memW_" select="($BLKD_MOD_W * $mods_w_)"/>
	<xsl:variable name="memH_" select="($BLKD_MOD_H * $mods_h_)"/>
	
	<xsl:variable name="symbol_name_">
		<xsl:call-template name="_gen_Stack_SymbolName"> 
			<xsl:with-param name="iHorizIdx" select="@STACK_HORIZ_INDEX"/>
			<xsl:with-param name="iVertiIdx" select="@SHAPE_VERTI_INDEX"/>
		</xsl:call-template>		
	</xsl:variable>
	
		
    <symbol id="{$symbol_name_}">
		
		<rect x="0"
		      y="0"
			  rx="6" 
			  ry="6" 
		      width = "{$memW_ + 4}"
		      height= "{$memH_ + 4}"
			  style="fill:{$peri_col_}; stroke:{$peri_col_}; stroke-width:2"/>		
			  

		<!-- Draw the memory block-->		  
		<xsl:choose>
			
		<xsl:when test="$mods_w_ = 1">
			
			<xsl:for-each select="MODULE[(@MODCLASS='MEMORY')]">	
				<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 	<use  x="2"  
				      y="{$BLKD_MOD_H + 2}"  
				      xlink:href="#symbol_{$modInst_}"/> 
			</xsl:for-each>
		
		
		<!-- Draw the memory controllers-->		  
			<xsl:for-each select="MODULE[not(@MODCLASS='MEMORY')]">	
				<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 	<use  x="2"  
				   	  y="0"  
				      xlink:href="#symbol_{$modInst_}"/> 
			</xsl:for-each>
		</xsl:when>	
		
		<xsl:when test="$mods_w_ &gt; 1">
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(@MODCLASS = 'MEMORY')]">
			
				<xsl:variable name="modInst_" select="@INSTANCE"/>
			
				 <use  x="{ceiling($memW_ div 2) - ($BLKD_MOD_W div 2)}"  
				   	   y="{$BLKD_MOD_H + 2}"  
				   	   xlink:href="#symbol_{$modInst_}"/> 
			</xsl:for-each>
		
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(not(@MODCLASS='MEMORY') and (@ORIENTED = 'WEST'))]">
				<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 	<use  x="0"  
				      y="0"  
				      xlink:href="#symbol_{$modInst_}"/> 
			</xsl:for-each>
		
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(not(@MODCLASS='MEMORY') and (@ORIENTED = 'EAST'))]">
				<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 	<use  x="{$BLKD_MOD_W}"  
				      y="0"  
				      xlink:href="#symbol_{$modInst_}"/> 
			</xsl:for-each>
		
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(not(@MODCLASS='MEMORY') and (@ORIENTED = 'CENTER'))]">	
				<xsl:variable name="modInst_" select="@INSTANCE"/>
			
			 	<use  x="{ceiling($memW_ div 2) - ($BLKD_MOD_W div 2)}"  
				      y="0"  
				   	  xlink:href="#symbol_{$modInst_}"/> 
		    </xsl:for-each>
			
		</xsl:when>	
		</xsl:choose>
			  
	</symbol>			  
	
</xsl:template>	
	
	
<xsl:template name="Define_StandAlone_MPMC"> 
	
<!--	
	<xsl:param name="drawarea_w"  select="500"/>
	<xsl:param name="drawarea_h"  select="500"/>
-->	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/MPMCSHAPE">
		
		<xsl:variable name="mpmcInst_" select="@INSTANCE"/>
		<xsl:variable name="mpmcType_" select="/EDKSYSTEM/MODULES/MODULE[@INSTANCE=$mpmcInst_]/@MODTYPE"/>
<!--		
		<xsl:message>Drawing instance <xsl:value-of select="$mpmcInst_"/></xsl:message>
-->		
		
		<xsl:variable name="mpmc_w_"  select="($G_total_drawarea_W - ($BLKD_INNER_GAP * 2))"/>
		<xsl:variable name="label_y_"  select="ceiling($BLKD_MPMC_MOD_H div 2) - ceiling($BLKD_MOD_LABEL_H div 2)"/>
		
		<symbol id="mpmcmodule_{$mpmcInst_}">
			<rect x="0"
		          y="0"
		          width = "{$mpmc_w_}"
		          height= "{$BLKD_MPMC_MOD_H}"
			      style="fill:{$COL_MPMC_BG}; stroke:{$COL_BLACK}; stroke-width:2"/>
			  
		    <rect x="{$BLKD_MOD_LANE_H}"
		          y="{$label_y_}"
			      rx="3"
			      ry="3"
		          width= "{$BLKD_MOD_LABEL_W}"
		          height="{$BLKD_MOD_LABEL_H}"
			      style="fill:{$COL_WHITE}; stroke:none;"/>
			
			<text class="bciptype" 
				  x="{ceiling(($BLKD_MOD_LANE_H + $BLKD_MOD_LABEL_W) div 2)}"
				  y="{$label_y_ + 8}">
					<xsl:value-of select="$mpmcType_"/>
			</text>
				
			<text class="bciplabel" 
				  x="{ceiling(($BLKD_MOD_LANE_H + $BLKD_MOD_LABEL_W) div 2)}"
				  y="{$label_y_ + 16}">
					<xsl:value-of select="$mpmcInst_"/>
		   </text>
			
			<text class="mpmctitle" 
				  x="{ceiling($mpmc_w_ div 2)}"
				  y="{$label_y_ + 16}">MPMC Module Interface</text>
<!--			
-->	
	   
		</symbol>	
		
	</xsl:for-each>
	
</xsl:template>	
	

<!-- ======================= END DEF FUNCTIONS ============================ -->

<!-- ======================= UTILITY FUNCTIONS ============================ -->

<xsl:template name="_draw_InterruptSource">

	<xsl:param name="iIntr_X"   select="0"/>
	<xsl:param name="iIntr_Y"   select="0"/>
	<xsl:param name="iIntr_PRI" select="0"/>
	<xsl:param name="iIntr_IDX" select="0"/>
	<xsl:param name="iIntr_COL" select="$COL_BLKD_INTR_0"/>
	
		<rect  
			x="{$iIntr_X}"
			y="{$iIntr_Y}"
			rx="3"
			ry="3"
			width= "{$BLKD_INTR_W}" 
			height="{ceiling($BLKD_INTR_H div 2)}" style="fill:{$iIntr_COL}; stroke:none; stroke-width:1"/> 
			
		<line x1="{$iIntr_X + ceiling($BLKD_INTR_W div 2)}" 
			  y1="{$iIntr_Y}"
			  x2="{$iIntr_X + ceiling($BLKD_INTR_W div 2)}" 
			  y2="{$iIntr_Y + ceiling($BLKD_INTR_H div 2)}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<xsl:variable name="txt_ofs_">
			<xsl:if test="($iIntr_PRI &gt; 9)">4.5</xsl:if>
			<xsl:if test="not($iIntr_PRI &gt; 9)">0</xsl:if>
		</xsl:variable>	  
		
		<text class="intrsymbol" 
			  x="{$iIntr_X + 2 - $txt_ofs_}"
			  y="{$iIntr_Y + 8}">
				<xsl:value-of select="$iIntr_PRI"/>
		</text>
			
		<text class="intrsymbol" 
			  x="{$iIntr_X + 2 + ceiling($BLKD_INTR_W div 2)}"
			  y="{$iIntr_Y + 8}">
				<xsl:value-of select="$iIntr_IDX"/>
		</text>
			
</xsl:template>

<xsl:template name="_draw_InterruptCntrl">

	<xsl:param name="iIntr_X"   select="0"/>
	<xsl:param name="iIntr_Y"   select="0"/>
	<xsl:param name="iIntr_IDX" select="0"/>
	<xsl:param name="iIntr_COL" select="$COL_BLKD_INTR_0"/>
	
		<rect  
			x="{$iIntr_X}"
			y="{$iIntr_Y}"
			rx="3"
			ry="3"
			width= "{ceiling($BLKD_INTR_W div 2)}" 
			height="{$BLKD_INTR_H}" style="fill:{$iIntr_COL}; stroke:none; stroke-width:1"/> 
			
		<line x1="{$iIntr_X}" 
			  y1="{$iIntr_Y + ceiling($BLKD_INTR_H div 4)}"
			  x2="{$iIntr_X + ceiling($BLKD_INTR_W div 2)}" 
			  y2="{$iIntr_Y + ceiling($BLKD_INTR_H div 4)}" 
			  style="stroke:{$COL_BLACK};stroke-width:2"/>
			  
		<text class="intrsymbol" 
			  x="{$iIntr_X + 2}"
			  y="{$iIntr_Y + 8 + ceiling($BLKD_INTR_H div 2)}">
				<xsl:value-of select="$iIntr_IDX"/>
		</text>
			
</xsl:template>


<xsl:template name="_draw_InterruptedProc">

	<xsl:param name="iIntr_X"   select="0"/>
	<xsl:param name="iIntr_Y"   select="0"/>
	<xsl:param name="iIntr_IDX" select="0"/>
	<xsl:param name="iIntr_COL" select="$COL_BLKD_INTR_0"/>
	
		<rect  
			x="{$iIntr_X}"
			y="{$iIntr_Y}"
			rx="3"
			ry="3"
			width= "{ceiling($BLKD_INTR_W div 2)}" 
			height="{$BLKD_INTR_H}" style="fill:{$iIntr_COL}; stroke:none; stroke-width:1"/> 
			
		<line x1="{$iIntr_X}" 
			  y1="{$iIntr_Y + ceiling($BLKD_INTR_H div 4) - 2}"
			  x2="{$iIntr_X + ceiling($BLKD_INTR_W div 2)}" 
			  y2="{$iIntr_Y + ceiling($BLKD_INTR_H div 4) - 2}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<line x1="{$iIntr_X}" 
			  y1="{$iIntr_Y + ceiling($BLKD_INTR_H div 4) + 2}"
			  x2="{$iIntr_X + ceiling($BLKD_INTR_W div 2)}" 
			  y2="{$iIntr_Y + ceiling($BLKD_INTR_H div 4) + 2}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<text class="intrsymbol" 
			  x="{$iIntr_X + 2}"
			  y="{$iIntr_Y + 8 + ceiling($BLKD_INTR_H div 2)}">
				<xsl:value-of select="$iIntr_IDX"/>
		</text>
			
</xsl:template>

<xsl:template name="_calc_CStackShapesAbv_Height">
	<xsl:param name="iCStackIndex"  select="100"/>
	<xsl:param name="iCSactkMods_Y" select="1000"/>
	
<!--	
	<xsl:message>Stack Index <xsl:value-of select="$cstackIndex"/></xsl:message>
	
	<xsl:message>Stack Y <xsl:value-of select="$cstackModY"/></xsl:message>
-->	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@CSTACK_INDEX = $iCStackIndex)])">0</xsl:if>
	
	<xsl:if test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@CSTACK_INDEX = $iCStackIndex)]">
	
		<xsl:variable name="shapesAbv_Heights_">
			<CSTACK_MOD HEIGHT="0"/>
			
			<!-- Store the heights of all the peripherals above this one heights in a variable -->
			<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@CSTACK_INDEX = $iCStackIndex) and (@CSTACK_MODS_Y &lt; $iCStackMods_Y))]">
				
				<xsl:variable name="shapeHeight_">
					
					<xsl:choose>
						
						<xsl:when test="@MODCLASS = 'PERIPHERAL'">
							<xsl:call-template name="_calc_PeriShape_Height">	
								<xsl:with-param name="iShapeInst" select="MODULE/@INSTANCE"/>
							</xsl:call-template>	
						</xsl:when>
						
						<xsl:when test="@MODCLASS = 'MEMORY_UNIT'">
							<xsl:call-template name="_calc_MemoryUnit_Height">	
								<xsl:with-param name="iShapeId" select="@SHAPE_ID"/>
							</xsl:call-template>	
						</xsl:when>
						
						<xsl:otherwise>0</xsl:otherwise>
					</xsl:choose>
				</xsl:variable>
				
<!--				
				<xsl:message>Calculated height of cstack shape of type <xsl:value-of select="@MODCLASS"/> as <xsl:value-of select="$shapeHeight_"/></xsl:message>
-->			
				
				<CSTACK_MOD HEIGHT="{$shapeHeight_ + $BLKD_BIF_H}"/>
			</xsl:for-each>
		</xsl:variable>
		
<!--		
		<xsl:message>Calculated height of cstack as <xsl:value-of select="sum(exsl:node-set($shapesAbv_Heights_)/CSTACK_MOD/@HEIGHT)"/></xsl:message>
-->		
		
		<xsl:value-of select="sum(exsl:node-set($shapesAbv_Heights_)/CSTACK_MOD/@HEIGHT)"/>
	</xsl:if>
	
</xsl:template>


<xsl:template name="_calc_PeriShape_Height">
	<xsl:param name="iShapeInst"  select="'_shape_'"/>
	
<!--	
	<xsl:message>Calculating height of <xsl:value-of select="$shapeInst"/></xsl:message>
-->	
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H) and not(/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H)">0</xsl:if>
	
	<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H)">
		<xsl:variable name="bifs_h_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H"/>
		
		<xsl:value-of select="($BLKD_MOD_LABEL_H + ($BLKD_BIF_H * $bifs_h_) + ($BLKD_MOD_BIF_GAP_V * $bifs_h_) + ($BLKD_MOD_LANE_H * 2))"/>
	</xsl:if>
	
	<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H)">
		<xsl:variable name="bifs_h_" select="/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H"/>
		
		<xsl:value-of select="($BLKD_MOD_LABEL_H + ($BLKD_BIF_H * $bifs_h_) + ($BLKD_MOD_BIF_GAP_V * $bifs_h_) + ($BLKD_MOD_LANE_H * 2))"/>
	</xsl:if>
	
	<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H)">
		<xsl:variable name="bifs_h_" select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $iShapeInst)]/@BIFS_H"/>
		
		<xsl:value-of select="($BLKD_MOD_LABEL_H + ($BLKD_BIF_H * $bifs_h_) + ($BLKD_MOD_BIF_GAP_V * $bifs_h_) + ($BLKD_MOD_LANE_H * 2))"/>
	</xsl:if>
	
</xsl:template>
	
<xsl:template name="_calc_Shape_Height">
	<xsl:param name="iShapeId"  select="_shape_"/>
	
<!--	
	<xsl:message>Calculating height of <xsl:value-of select="$shapeId"/></xsl:message>
-->	
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)])">0</xsl:if>
	
	<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE/@BIFS_H)">
		<xsl:variable name="bifs_h_" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE/@BIFS_H"/>
		
		<xsl:value-of select="($BLKD_MOD_LABEL_H + ($BIF_H * $bifs_h_) + ($BLKD_MOD_BIF_GAP_V * $bifs_h_) + ($BLKD_MOD_LANE_H * 2))"/>
	</xsl:if>
	
</xsl:template>


<xsl:template name="_calc_MemoryUnit_Height">
	<xsl:param name="iShapeId"  select="1000"/>
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)])">0</xsl:if>
	
	<xsl:if test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]">
	
		<!-- Store the memory controller heights in a variable -->	
		<xsl:variable name="memC_heights_">	
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(@MODCLASS = 'MEMORY_CNTLR')])">
				<MEM_CNTLR INSTANCE="{@INSTANCE}" HEIGHT="0"/>
			</xsl:if>
			
			<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(@MODCLASS = 'MEMORY_CNTLR')])">
				<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[(@MODCLASS = 'MEMORY_CNTLR')]">
					<xsl:variable name="memC_height_">
						<xsl:call-template name="_calc_PeriShape_Height">	
							<xsl:with-param name="iShapeInst" select="@INSTANCE"/>
						</xsl:call-template>
					</xsl:variable>
					<MEM_CNTLR INSTANCE="{@INSTANCE}" HEIGHT="{$memC_height_}"/>
				</xsl:for-each>
			</xsl:if>
		</xsl:variable>
		
		<!-- Store the bram heights in a variable -->	
		<xsl:variable name="bram_heights_">	
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[not(@MODCLASS = 'MEMORY_CNTLR')])">
				<BRAM INSTANCE="{@INSTANCE}" HEIGHT="0"/>
			</xsl:if>
			<xsl:if test="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[not(@MODCLASS = 'MEMORY_CNTLR')]">
				<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@SHAPE_ID = $iShapeId)]/MODULE[not(@MODCLASS = 'MEMORY_CNTLR')]">
					<xsl:variable name="bram_height_">
						<xsl:call-template name="_calc_PeriShape_Height">	
							<xsl:with-param name="iShapeInst" select="@INSTANCE"/>
						</xsl:call-template>
					</xsl:variable>
					<BRAM INSTANCE="{@INSTANCE}" HEIGHT="{$bram_height_}"/>
				</xsl:for-each>
			</xsl:if>
		</xsl:variable>
		
		<!-- Select the maximum of them -->
		<xsl:variable name="max_bram_height_" select="math:max(exsl:node-set($bram_heights_)/BRAM/@HEIGHT)"/>
		<xsl:variable name="max_memC_height_" select="math:max(exsl:node-set($memC_heights_)/MEM_CNTLR/@HEIGHT)"/>
		
		<xsl:value-of select="$max_bram_height_ + $max_memC_height_"/>
	</xsl:if>

</xsl:template>


<xsl:template name="_calc_SbsBucket_Height">
	<xsl:param name="iBucketId"  select="100"/>
	
<!--	
	<xsl:message>Looking of height of bucket <xsl:value-of select="$bucketId"/></xsl:message>
-->	
	<xsl:variable name="bkt_gap_" select="$BLKD_BIF_H"/>
	
	<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@BUSINDEX = $iBucketId)])">0</xsl:if>
	
	<xsl:if test="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@BUSINDEX = $iBucketId)]">
		<xsl:variable name="mods_h_" select="/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@BUSINDEX = $iBucketId)]/@MODS_H"/>
		
		<xsl:value-of select="((($BLKD_MOD_BKTLANE_H * 2) + ((($BLKD_MOD_H + $BLKD_BIFC_H) * $mods_h_) + ($BLKD_MOD_BUCKET_G * ($mods_h_ - 1)))) + $bkt_gap_)"/>
	</xsl:if>
</xsl:template>
	
<!--
	===============================================
	
		Symbol Naming Functions
	
	===============================================
-->		
	
	
<xsl:template name="_gen_Proc_StackName">
<xsl:param name="iProcInst"  select="'_unknown_'"/>
symbol_STACK_<xsl:value-of select="$iProcInst"/>
</xsl:template>
	
<xsl:template name="_gen_Proc_GroupName">
<xsl:param name="iProcInst"  select="'_unknown_'"/>
symbol_GROUP_<xsl:value-of select="$iProcInst"/>
</xsl:template>
	
	
<xsl:template name="_gen_Space_Name"><xsl:param name="iStackToEast"    select="'NONE'"/><xsl:param name="iStackToWest"  select="'NONE'"/>symbol_SPACE_WEST_<xsl:value-of select="$iStackToWest"/>_EAST_<xsl:value-of select="$iStackToEast"/></xsl:template>
<xsl:template name="_gen_Stack_Name"><xsl:param name="iHorizIdx"       select="'_unknown_'"/>symbol_STACK_<xsl:value-of select="$iHorizIdx"/></xsl:template>
<xsl:template name="_gen_Stack_SymbolName"><xsl:param name="iHorizIdx" select="'_unknown_'"/><xsl:param name="iVertiIdx" select="'_unknown_'"/>symbol_STACK_<xsl:value-of select="$iHorizIdx"/>_SHAPE_<xsl:value-of select="$iVertiIdx"/></xsl:template>
	

<!-- ======================= END UTILITY FUNCTIONS  ======================= -->
</xsl:stylesheet>

