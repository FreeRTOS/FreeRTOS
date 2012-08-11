<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
                
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
		   
<xsl:variable name="G_ROOT" select="/"/>			

<xsl:variable name="G_BIFTYPES">

	<BIFTYPE TYPE="SLAVE"/>
	<BIFTYPE TYPE="MASTER"/>
	<BIFTYPE TYPE="MASTER_SLAVE"/>
	
	<BIFTYPE TYPE="TARGET"/>
	<BIFTYPE TYPE="INITIATOR"/>
	
	<BIFTYPE TYPE="MONITOR"/>
	
	<BIFTYPE TYPE="USER"/>
	
</xsl:variable>	

<xsl:variable name="G_BUSSTDS">
	
	<BUSSTD NAME="XIL"/>
	<BUSSTD NAME="OCM"/>
	<BUSSTD NAME="OPB"/>
	<BUSSTD NAME="LMB"/>
	<BUSSTD NAME="FSL"/>
	<BUSSTD NAME="DCR"/>
	<BUSSTD NAME="FCB"/>
	<BUSSTD NAME="PLB"/>
	<BUSSTD NAME="PLBV46"/>
	<BUSSTD NAME="PLBV46_P2P"/>

	<BUSSTD NAME="USER"/>
</xsl:variable>


</xsl:stylesheet>
