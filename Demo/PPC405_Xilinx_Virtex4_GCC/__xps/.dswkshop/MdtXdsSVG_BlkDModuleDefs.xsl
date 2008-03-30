<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
                
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
			

<xsl:template name="Print_BlkdModuleDefs">
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

</xsl:stylesheet>
