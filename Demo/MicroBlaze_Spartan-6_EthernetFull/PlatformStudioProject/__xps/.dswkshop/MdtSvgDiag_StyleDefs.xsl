<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
	   xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
       xmlns:exsl="http://exslt.org/common"
       xmlns:dyn="http://exslt.org/dynamic"
       xmlns:math="http://exslt.org/math"
       xmlns:xlink="http://www.w3.org/1999/xlink"
       extension-element-prefixes="math dyn exsl xlink">
                
<!-- 
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
-->                
 
<!-- 
	======================================================
			Function to put TEXT CSS and other Internal
		    Styling properties directly into the output 
		    svg. The Qt 4.3 Renderer 
			cannot handle separate CSS StyleSheets
	======================================================
-->	
<xsl:template name="F_WriteText">

	<xsl:param name="iClass"  select="'_UNKNOWN_'"/>
	<xsl:param name="iText"  select="' '"/>
	<xsl:param name="iX"	 select="'0'"/>
	<xsl:param name="iY"	 select="'0'"/>
	
<!--
	<xsl:message>TEXT  <xsl:value-of select="$iText"/></xsl:message>	
	<xsl:message>CLASS <xsl:value-of select="$iClass"/></xsl:message>	
-->	

	<xsl:element name="text">
		<xsl:attribute name="x"><xsl:value-of select="$iX"/></xsl:attribute>
		<xsl:attribute name="y"><xsl:value-of select="$iY"/></xsl:attribute>
		
		<xsl:choose>
			
			<xsl:when test="$iClass = 'sharedbus_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'12pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>

			<xsl:when test="$iClass = 'p2pbus_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'p2pbus_label_horiz'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'12pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="writing-mode"><xsl:value-of select="'tb'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			
			<xsl:when test="$iClass = 'bif_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
		
			<xsl:when test="$iClass = 'bc_ipinst'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'bc_iptype'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_XLNX"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'iogrp_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_IORING"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'normal'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'mpmc_title'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_WHITE"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'16pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'oblique'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'mpmc_biflabel'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_WHITE"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'normal'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'intr_symbol'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'bkt_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'9pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'normal'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'ipclass_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'9pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'normal'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'key_header'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			<xsl:when test="$iClass = 'key_title'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_XLNX"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'14pt'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>
			
			<xsl:when test="$iClass = 'key_label'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			<xsl:when test="$iClass = 'key_label_small'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'900'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			
			<xsl:when test="$iClass = 'key_label_ul'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="text-decoration"><xsl:value-of select="'underline'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			
			<xsl:when test="$iClass = 'ipd_portlabel'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'normal'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			<xsl:when test="$iClass = 'ipd_biflabel'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'normal'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			<xsl:when test="$iClass = 'ipd_iptype'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_XLNX"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Verdana Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			<xsl:when test="$iClass = 'ipd_ipname'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'8pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		
			
			<xsl:when test="$iClass = 'blkd_spec_name'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'start'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		

			<xsl:when test="$iClass = 'blkd_spec_value_mid'">
				<xsl:attribute name="fill"><xsl:value-of select="$COL_BLACK"/></xsl:attribute>
				<xsl:attribute name="stroke"><xsl:value-of select="'none'"/></xsl:attribute>
				<xsl:attribute name="font-size"><xsl:value-of select="'10pt'"/></xsl:attribute>
				<xsl:attribute name="font-style"><xsl:value-of select="'italic'"/></xsl:attribute>
				<xsl:attribute name="font-weight"><xsl:value-of select="'bold'"/></xsl:attribute>
				<xsl:attribute name="text-anchor"><xsl:value-of select="'middle'"/></xsl:attribute>
				<xsl:attribute name="font-family"><xsl:value-of select="'Courier Arial Helvetica san-serif'"/></xsl:attribute>
			</xsl:when>		

			<xsl:otherwise><xsl:message>UNKNOWN Text style class <xsl:value-of select="$iClass"/></xsl:message></xsl:otherwise>
		</xsl:choose>
		
		<xsl:value-of select="$iText"/>
	</xsl:element>
	
</xsl:template>
	
</xsl:stylesheet>

<!--
	text.ioplblgrp {
		fill:        #000088;
		stroke:      none;
		font-size:   10pt; 
		font-style:  normal;
		font-weight: 900;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}
	text.iplabel {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic;
		font-weight: 800;
		text-anchor: middle;
		font-family: Courier Arial Helvetica sans-serif;
	}
		
	text.iptype {
		fill:        #AA0017;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic;
		font-weight: bold;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}	
	
	text.busintlabel {
		fill:        #810017;
		stroke:      none;
		font-size:   7pt; 
		font-style:  italic;
		font-weight: 900;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.mpmcbiflabel {
		fill:        #FFFFFF;
		stroke:      none;
		font-size:   6pt; 
		font-style:  normal;
		font-weight: 900;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.buslabel {
		fill:        #CC3333;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic;
		font-weight: bold;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}



	text.ipclass {
		fill:        #000000;
		stroke:      none;
		font-size:   7pt; 
		font-style:  normal;
		font-weight: bold;
		text-anchor: start;
		font-family: Times Arial Helvetica sans-serif;
	}

	text.procclass {
		fill:        #000000;
		stroke:      none;
		font-size:   7pt; 
		font-style:  normal;
		font-weight: bold;
		text-anchor: middle;
		font-family: Times Arial Helvetica sans-serif;
	}
		
		
	text.portlabel {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  normal;
		font-weight: bold;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.ipdbiflbl {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  normal;
		font-weight: bold;
		font-family: Verdana Arial Helvetica sans-serif;
	}
		
	text.mmMHeader {
		fill:        #FFFFFF;
		stroke:      none;
		font-size:   10pt; 
		font-style:  normal;
		font-weight: bold;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.mmSHeader {
		fill:        #810017;
		stroke:      none;
		font-size:   10pt; 
		font-style:  normal;
		font-weight: bold;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}



	text.dbglabel {
		fill:        #555555;
		stroke:      none;
		font-size:   8pt; 
		font-style:  normal;
		font-weight: 900;
		text-anchor: middle;
		font-family: Times Arial Helvetica sans-serif;
	}

	text.iopnumb {
		fill:        #555555;
		stroke:      none;
		font-size:   10pt; 
		font-style:  normal;
		font-weight: 900;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}



	tspan.iopgrp {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  normal;
		font-weight: 900;
		text-anchor: middle;
		baseline-shift:super;
		font-family: Arial Courier san-serif;
	}


	text.biflabel {
		fill:        #000000;
		stroke:      none;
		font-size:   6pt; 
		font-style:  normal;
		font-weight: 900;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;

	}

	text.p2pbuslabel {
		fill:         #000000;
		stroke:       none;
		font-size:    10pt; 
		font-style:   italic;
		font-weight:  bold; 
		text-anchor:  start;
		writing-mode: tb;
		font-family:  Verdana Arial Helvetica sans-serif;
	}

	text.mpbuslabel {
		fill:         #000000;
		stroke:       none;
		font-size:    6pt; 
		font-style:   italic;
		font-weight:  bold; 
		text-anchor:  start;
		writing-mode: tb;
		font-family:  Verdana Arial Helvetica sans-serif;
	}


	text.sharedbuslabel {
		fill:         #000000;
		stroke:       none;
		font-size:    10pt; 
		font-style:   italic;
		font-weight:  bold; 
		text-anchor:  start;
		font-family:  Verdana Arial Helvetica sans-serif;
	}


	text.splitbustxt {
		fill:        #000000;
		stroke:      none;
		font-size:   6pt; 
		font-style:  normal;
		font-weight: bold;
		text-anchor: middle;
		font-family: sans-serif;
	}

	text.horizp2pbuslabel {
		fill:         #000000;
		stroke:       none;
		font-size:    6pt; 
		font-style:   italic;
		font-weight:  bold; 
		text-anchor:  start;
		font-family:  Verdana Arial Helvetica sans-serif;
	}



	text.keytitle {
		fill:        #AA0017;
		stroke:      none;
		font-size:   12pt; 
		font-weight: bold;
		text-anchor: middle;
		font-family: Arial Helvetica sans-serif;
	}

	text.keyheader {
		fill:        #000000;
		stroke:      none;
		font-size:   10pt; 
		font-weight: bold;
		text-anchor: middle;
		font-family: Arial Helvetica sans-serif;
	}

	text.keylabel {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic; 
		font-weight: bold;
		text-anchor: start;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.keylblul {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic; 
		font-weight: bold;
		text-anchor: start;
		text-decoration: underline;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.specsheader {
		fill:        #000000;
		stroke:      none;
		font-size:   10pt; 
		font-weight: bold;
		text-anchor: start;
		font-family: Arial Helvetica sans-serif;
	}

	text.specsvalue {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic; 
		font-weight: bold;
		text-anchor: start;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.specsvaluemid {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-style:  italic; 
		font-weight: bold;
		text-anchor: middle;
		font-family: Verdana Arial Helvetica sans-serif;
	}

	text.intrsymbol {
		fill:        #000000;
		stroke:      none;
		font-size:   8pt; 
		font-weight: bold;
		text-anchor: start;
		font-family: Arial Helvetica sans-serif;
	}

-->