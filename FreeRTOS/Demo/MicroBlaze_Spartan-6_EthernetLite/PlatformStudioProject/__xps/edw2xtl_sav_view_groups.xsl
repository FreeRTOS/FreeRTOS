<!DOCTYPE stylesheet [
    <!ENTITY ALPUPRS "ABCDEFGHIJKLMNOPQRSTUVWXYZ">
    <!ENTITY ALPLWRS "abcdefghijklmnopqrstuvwxyz">
    <!ENTITY UPR2LWS " '&ALPUPRS;' , '&ALPLWRS;' ">
    
    <!ENTITY HEXUPPER "ABCDEFxx0123456789">
    <!ENTITY HEXLOWER "abcdefxX0123456789">
    <!ENTITY HEXU2L " '&HEXLOWER;' , '&HEXUPPER;' ">
    
    <!ENTITY DIV2SLSH " 'div' , '&#047;' ">     
    
    <!ENTITY NOT_ELM_CONN "not(name() = 'PARAMETER') and not(name() = 'PORT')          and not(name() = 'BUSINTERFACE')">
    <!ENTITY NOT_BEF_CONN "not(name() = 'DOCUMENT')  and not(name() = 'DOCUMENTATION') and not(name() = 'DESCRIPTION') and not(name() = 'LICENSEINFO')">
    <!ENTITY NOT_AFT_CONN "not(name() = 'MEMORYMP') and not(name() = 'PERIPHERALS')   and not(name() = 'INTERRUPTINFO')">
]>

<!-- ==============================================================
 	 This XSL file converts BLOCK xml to SAV XTeller 
	============================================================== -->	
<xsl:stylesheet 
           version="1.0"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:dyn="http://exslt.org/dynamic"
           xmlns:math="http://exslt.org/math"
           xmlns:xlink="http://www.w3.org/1999/xlink"
           extension-element-prefixes="math exsl dyn xlink">
           
<xsl:output method="xml" 
            version="1.0" 
            indent="yes"
            encoding="UTF-8"/> 
<!--
    ===================================================
    	THE MAIN TEMPLATE FOR PORT VIEW SELECTED FOCUS
    ===================================================
-->
<xsl:template name="WRITE_VIEW_PORT_FOCUSED">
	<xsl:choose>
	 	<xsl:when test="$G_ROOT/SAV/@MODE = 'TREE'">
 			<xsl:call-template name="WRITE_VIEW_EXTP_TREE_SET"/>
		</xsl:when>
	 	<xsl:when test="$G_ROOT/SAV/@MODE = 'FLAT'">
 			<xsl:call-template name="WRITE_VIEW_EXTP_FLAT_SET"/>
		</xsl:when>
	</xsl:choose>
  	<xsl:apply-templates  select="$G_SYS_MODS/MODULE" mode="_port_view_focusing_on_selected"/>
</xsl:template>	


<!--
    ====================================================
    	THE MAIN TEMPLATE FOR BIF VIEW BUS FOCUS
    ====================================================
-->
<xsl:template name="WRITE_VIEW_BIF_FOCUS_ON_BUSES">

<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>Focusing on busses</xsl:message></xsl:if>
<!--
	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
		<xsl:with-param name="iModules" select="$G_GROUPS"/>
	</xsl:call-template>
  -->
  <xsl:apply-templates  select="$G_SYS_MODS/MODULE" mode="_bif_view_focusing_on_buses"/>
	<xsl:if test="$G_ROOT/SAV/@MODE = 'TREE'"> <!--  The separator -->
		<xsl:element name="SET">
		
			<xsl:attribute name="ID">MODULES WITH POTENTIAL CONNECTIONS TO FOCUSED BUS</xsl:attribute>
			<xsl:attribute name="CLASS">SEPARATOR</xsl:attribute>
			<xsl:element name="VARIABLE">
				<xsl:attribute name="VIEWDISP">Name</xsl:attribute>
				<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
				<xsl:attribute name="NAME">Name</xsl:attribute>
				<xsl:attribute name="VALUE">POTENTIAL MODULES BELOW HERE</xsl:attribute>
			</xsl:element>
			<xsl:element name="VARIABLE">
	       		<xsl:attribute name="VIEWDISP">IP Type</xsl:attribute>
	       		<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	       		<xsl:attribute name="NAME">MODTYPE</xsl:attribute>
	       		<xsl:attribute name="VALUE"></xsl:attribute>
			</xsl:element>
			<xsl:element name="VARIABLE">
	       	<xsl:attribute name="VIEWDISP">IP Version</xsl:attribute>
		       	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
		       	<xsl:attribute name="NAME">HWVERSION</xsl:attribute>
		       	<xsl:attribute name="VALUE"></xsl:attribute>
				</xsl:element>	 		
			<xsl:element name="VARIABLE">
		       	<xsl:attribute name="VIEWDISP">IP Classification</xsl:attribute>
		       	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
		       	<xsl:attribute name="NAME">IPCLASS</xsl:attribute>
		       	<xsl:attribute name="VALUE"></xsl:attribute>
			</xsl:element>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE"></xsl:attribute>
	        	<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
	        	<xsl:attribute name="VALUE"></xsl:attribute>
	 		</xsl:element>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Type</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">TYPE</xsl:attribute>
	        	<xsl:attribute name="VALUE"></xsl:attribute>
	 		</xsl:element>	 		
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Bus Standard</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">BUSSTD</xsl:attribute>
	        	<xsl:attribute name="VALUE"></xsl:attribute>
	 		</xsl:element>			 			
		</xsl:element>
	</xsl:if>  
</xsl:template>	

<!--
    ====================================================
    	THE MAIN TEMPLATE FOR BIF VIEW PROCESSOR FOCUS
    ====================================================
-->
<xsl:template name="WRITE_VIEW_BIF_FOCUS_ON_PROCS">

	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
		<xsl:with-param name="iModules" select="$G_GROUPS"/>
	</xsl:call-template>
	
	<xsl:if test="$G_ROOT/SAV/@MODE = 'TREE'"> <!--  The separator -->
		<xsl:element name="SET">
		
			<xsl:attribute name="ID">MODULES WITH POTENTIAL CONNECTIONS TO THIS SUBSYSTEM</xsl:attribute>
			<xsl:attribute name="CLASS">SEPARATOR</xsl:attribute>
			<xsl:element name="VARIABLE">
				<xsl:attribute name="VIEWDISP">Name</xsl:attribute>
				<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
				<xsl:attribute name="NAME">Name</xsl:attribute>
				<xsl:attribute name="VALUE">POTENTIAL MODULES BELOW HERE</xsl:attribute>
			</xsl:element>
			<xsl:element name="VARIABLE">
	       		<xsl:attribute name="VIEWDISP">IP Type</xsl:attribute>
	       		<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	       		<xsl:attribute name="NAME">MODTYPE</xsl:attribute>
	       		<xsl:attribute name="VALUE"></xsl:attribute>
			</xsl:element>
			<xsl:element name="VARIABLE">
	       	<xsl:attribute name="VIEWDISP">IP Version</xsl:attribute>
		       	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
		       	<xsl:attribute name="NAME">HWVERSION</xsl:attribute>
		       	<xsl:attribute name="VALUE"></xsl:attribute>
				</xsl:element>	 		
			<xsl:element name="VARIABLE">
		       	<xsl:attribute name="VIEWDISP">IP Classification</xsl:attribute>
		       	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
		       	<xsl:attribute name="NAME">IPCLASS</xsl:attribute>
		       	<xsl:attribute name="VALUE"></xsl:attribute>
			</xsl:element>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE"></xsl:attribute>
	        	<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
	        	<xsl:attribute name="VALUE"></xsl:attribute>
	 		</xsl:element>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Type</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">TYPE</xsl:attribute>
	        	<xsl:attribute name="VALUE"></xsl:attribute>
	 		</xsl:element>	 		
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Bus Standard</xsl:attribute>
	        	
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">BUSSTD</xsl:attribute>
	        	<xsl:attribute name="VALUE"></xsl:attribute>
	 		</xsl:element>			 			
		</xsl:element>
	</xsl:if>
</xsl:template>

<!--
    ===============================================
    	COPY TRANSFORMS FOR FOCUSING IN BIF VIEW 
    ===============================================
-->

<!-- Root copy template for connected -->
<xsl:template match="node() | @*" mode="_bif_view_focusing_on_connected">
	<xsl:copy>
		<xsl:apply-templates select="@* | node()" mode="_bif_view_focusing_on_connected"/>
	</xsl:copy>
</xsl:template>

<!-- Root copy template for potentials -->
<xsl:template match="node() | @*" mode="_bif_view_focusing_on_potentials">
	<xsl:copy>
		<xsl:apply-templates select="@* | node()" mode="_bif_view_focusing_on_potentials"/>
	</xsl:copy>
</xsl:template>


<xsl:template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES"> <!--  Recursive  !! -->
	<xsl:param name="iModules"/>
	
	<xsl:for-each select="$iModules/BLOCK[@ID and not(BLOCK) and not(@C)]">
    	<xsl:variable name="m_id_" 		 			select="@ID"/>
   		<xsl:if test="(count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME = $m_id_]) &gt; 0)">
   			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING BUS <xsl:value-of select="@ID"/></xsl:message></xsl:if>
    			<xsl:variable name="m_module_"   			select="$G_SYS_MODS/MODULE[@INSTANCE = $m_id_]"/>
      			<xsl:apply-templates  select="$m_module_"   mode="_bif_view_focusing_on_connected"/>
     	</xsl:if>
    </xsl:for-each> 
	    
	<xsl:for-each select="$iModules/BLOCK[@ID and BLOCK]">
		<xsl:choose>
		
			<!--  An actual module that needs to be written -->	
			<xsl:when test="not(starts-with(@ID,'__')) and BLOCK[@C] and (not(BLOCK/BLOCK) or BLOCK/BLOCK[@CP])">
  				
  				<xsl:variable name="m_id_"          select="@ID"/>
		    	<xsl:variable name="m_module_"      select="$G_SYS_MODS/MODULE[@INSTANCE = $m_id_]"/>
       			<xsl:apply-templates select="$m_module_"  mode="_bif_view_focusing_on_connected"/>
		    </xsl:when>
		    
			<xsl:when test="starts-with(@ID,'__GROUP_PROCESSOR__.') or starts-with(@ID,'__GROUP_MASTER__.')">
			
				<!-- 
					<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>MASTER GROUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				 -->
				
  				<xsl:variable name="master_id_">
  					<xsl:choose>
  						<xsl:when test="starts-with(@ID,'__GROUP_MASTER__.')"><xsl:value-of    select="substring-after(@ID,'__GROUP_MASTER__.')"/> </xsl:when>
  						<xsl:when test="starts-with(@ID,'__GROUP_PROCESSOR__.')"><xsl:value-of select="substring-after(@ID,'__GROUP_PROCESSOR__.')"/> </xsl:when>
  					</xsl:choose>
  				</xsl:variable>
  				
  				<xsl:variable name="num_focused_on_" select="count($G_ROOT/SAV/MASTER[(@INSTANCE = $master_id_)])"/>	

				<xsl:choose>
					<xsl:when test="$num_focused_on_  &gt; 0">
						<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>CONNECTED MASTER GROUP <xsl:value-of select="$master_id_"/></xsl:message></xsl:if>
				 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
		   					<xsl:with-param name="iModules" select="self::node()"/>
		   				</xsl:call-template>
	   				</xsl:when>
	   				
					<xsl:otherwise>
						<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>POTENTIAL MASTER GROUP <xsl:value-of select="$master_id_"/></xsl:message></xsl:if>
				 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES">
		   					<xsl:with-param name="iModules" select="self::node()"/>
		   				</xsl:call-template>
					</xsl:otherwise>
				</xsl:choose>
  			</xsl:when>	
  			
  			<xsl:when test="starts-with(@ID,'__GROUP_SHARED__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>SHARED GROUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
  				<xsl:variable name="p_id_" select="substring-after(@ID,'__GROUP_SHARED__')"/>
  				
  				<xsl:variable name="num_focused_on_" select="count($G_ROOT/SAV/MASTER[contains($p_id_,@INSTANCE)])"/>	
				
				<xsl:choose>
					<xsl:when test="$num_focused_on_  &gt; 0">
				 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
		   					<xsl:with-param name="iModules" select="self::node()"/>
		   				</xsl:call-template>
	   				</xsl:when>
	   				
	 				<xsl:otherwise>
				 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES">
		   					<xsl:with-param name="iModules" select="self::node()"/>
		   				</xsl:call-template>
	 				</xsl:otherwise>
				</xsl:choose>
  			</xsl:when>	
  			
			<xsl:when test="starts-with(@ID,'__GROUP_MEMORY__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message> MEMORY GROUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
  				<xsl:variable name="m_id_" select="substring-after(@ID,'__GROUP_MEMORY__')"/>
  				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>	
			
			<xsl:when test="starts-with(@ID,'__GROUP_PERIPHERAL__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PERIPHERAL GROUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="starts-with(@ID,'__GROUP_SLAVES__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>SLAVE GROUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="(starts-with(@ID,'__GROUP_IP__') and not($G_ROOT/SAV/@VIEW = 'BUSINTERFACE'))">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>IP GROUP<xsl:value-of select="@ID"/></xsl:message></xsl:if>
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_CONNECTED_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="starts-with(@ID,'__GROUP_FLOATING__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>FLOATING GROUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>
			<xsl:otherwise>
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message> IGNORING <xsl:value-of select="@ID"/></xsl:message></xsl:if>
			</xsl:otherwise>			
		</xsl:choose>
	</xsl:for-each>
</xsl:template>	



<!--
    ===============================================
    	TRANSFORMS FOR FOCUSED POTENTIAL MODULES
    ===============================================
-->
<xsl:template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES"> <!--  Recursive  !! -->
	<xsl:param name="iModules"/>
	
	<!--  BUS -->
	<xsl:for-each select="$iModules/BLOCK[@ID and not(BLOCK) and not(@C)]">
    	<xsl:variable name="m_id_" 		 			select="@ID"/>
   		<xsl:if test="(count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME = $m_id_]) &gt; 0)">
   			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING BUS <xsl:value-of select="@ID"/></xsl:message></xsl:if>
    			<xsl:variable name="m_module_"   			select="$G_SYS_MODS/MODULE[@INSTANCE = $m_id_]"/>
      			<xsl:apply-templates  select="$m_module_"   mode="_bif_view_focusing_on_connected"/>
     	</xsl:if>
    </xsl:for-each>
    
	<!--  GROUP -->
	<xsl:for-each select="$iModules/BLOCK[@ID and BLOCK]">
		<xsl:choose>
			<xsl:when test="not(starts-with(@ID,'__')) and BLOCK[@C] and (not(BLOCK/BLOCK) or BLOCK/BLOCK[@CP])">
  				
  				<xsl:variable name="m_id_"      select="@ID"/>
		    	<xsl:variable name="m_module_"  select="$G_SYS_MODS/MODULE[@INSTANCE = $m_id_]"/>
   		    	<xsl:variable name="m_class_"   select="$m_module_/@MODCLASS"/>
		    	<xsl:choose>
			    	<xsl:when test ="not($m_class_ = 'PROCESSOR')">
				    	<xsl:variable name="potential_bifs_">
							<xsl:for-each select="$m_module_/BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
		  						<xsl:variable name="b_std_"  select="@BUSSTD"/>
		  						<xsl:variable name="b_bus_"  select="@BUSNAME"/>
								<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><CONNECTED/></xsl:if>
								<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD = $b_std_]) &gt; 0"><POTENTIAL/></xsl:if>
							</xsl:for-each>
		 	  			</xsl:variable>
		 	  			
		 	  			<xsl:variable name="num_potential_" select="count(exsl:node-set($potential_bifs_)/POTENTIAL)"/>	
		 	  			<xsl:variable name="num_connected_" select="count(exsl:node-set($potential_bifs_)/CONNECTED)"/>	
		 	  			
		 	  			<xsl:if test=" ($num_potential_ &gt; 0)">
		       				<xsl:apply-templates select="$m_module_" mode="_bif_view_focusing_on_potentials"/>
		 	  			</xsl:if>	
			    	</xsl:when>
			    	<xsl:when test="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $m_id_)]) &gt; 0">
						<xsl:if test="$G_DEBUG='TRUE'"><xsl:message> PERI PROCESSOR <xsl:value-of select="$m_id_"/></xsl:message></xsl:if>
						<xsl:apply-templates select="$m_module_" mode="_bif_view_focusing_on_potentials"/>
			    	</xsl:when>
		    	</xsl:choose>
		    </xsl:when>
		    
			<xsl:when test="starts-with(@ID,'__GROUP_MEMORY__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING MEMORY <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
  				<xsl:variable name="m_id_" select="substring-after(@ID,'__GROUP_MEMORY__')"/>
  				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>	
			
			<xsl:when test="starts-with(@ID,'__GROUP_PERIPHERAL__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING POTENTIAL GROUP OF PERIPHERALS <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="starts-with(@ID,'__GROUP_SLAVES__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING POTENTIAL GROUP OF SLAVES <xsl:value-of select="@ID"/></xsl:message></xsl:if>
				
		 	   	<xsl:call-template name="WRITE_VIEW_BIF_FOCUSED_POTENTIAL_MODULES">
   					<xsl:with-param name="iModules" select="self::node()"/>
   				</xsl:call-template>	
			</xsl:when>
			<xsl:otherwise>
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message> IGNORING <xsl:value-of select="@ID"/></xsl:message></xsl:if>
			</xsl:otherwise>
		</xsl:choose>
	</xsl:for-each>
</xsl:template>	

<!--
    +++++++++++++++++++++++++++++++++++++++++++++++++++++
    		      MODULE TEMPLATES
    +++++++++++++++++++++++++++++++++++++++++++++++++++++
-->

<!--
    ===================================================
    	THE MODULE TEMPLATE FOR PORT VIEW SELECTED FOCUS
    ===================================================
-->

<xsl:template match="MODULE" mode="_port_view_focusing_on_selected">
	<xsl:variable name="m_inst_" select="@INSTANCE"/>
	
	<xsl:if test="count($G_ROOT/SAV/SELECTED[(@INSTANCE = $m_inst_)]) &gt; 0">
		<xsl:choose>
 			<xsl:when test="$G_ROOT/SAV/@MODE = 'TREE'">
				<xsl:call-template name="WRITE_VIEW_PORT_TREE_SET">
					<xsl:with-param name="iModRef" select="self::node()"/>
				</xsl:call-template>	
			</xsl:when>		
		
			<xsl:when test="$G_ROOT/SAV/@MODE = 'FLAT'">
				<xsl:call-template name="WRITE_VIEW_PORT_FLAT_SET">
					<xsl:with-param name="iModRef" select="self::node()"/>
				</xsl:call-template>
			</xsl:when>
		</xsl:choose>
	</xsl:if>
</xsl:template>
 
<!--
    ===================================================
    	THE MODULE TEMPLATE FOR  BIF VIEW BUS FOCUS
    ===================================================
-->
<xsl:template match="MODULE" mode="_bif_view_focusing_on_buses">

	<xsl:variable name="m_instance_" select="@INSTANCE"/>
	<xsl:variable name="m_modclass_" select="@MODCLASS"/>
	
	<xsl:variable name="is_focused_bus_"  select="count($G_ROOT/SAV/BUS[(@INSTANCE = $m_instance_)])"/>
	
	<xsl:variable name="bif_scope_">
		<xsl:if test="$is_focused_bus_ = 0"> <!--  No need to waste time if we know its one of the focused bus -->
			<xsl:for-each select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
				<xsl:variable name="b_bus_"      		select="@BUSNAME"/>
				<xsl:variable name="b_bstd_"      		select="@BUSSTD"/>
				<xsl:variable name="b_on_focused_bus_"  select="count($G_ROOT/SAV/BUS[(@INSTANCE = $b_bus_)])"/>
				<xsl:variable name="b_of_focused_bstd_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD   = $b_bstd_])"/>
				<xsl:if test="$b_on_focused_bus_  &gt; 0"><CONNECTED/></xsl:if>
				<xsl:if test="$b_of_focused_bstd_ &gt; 0"><POTENTIAL/></xsl:if>
			</xsl:for-each>
		</xsl:if>
	</xsl:variable>
	
	<xsl:variable name="on_focused_bus_"  select="count(exsl:node-set($bif_scope_)/CONNECTED)"/>
	<xsl:variable name="of_focused_bstd_" select="count(exsl:node-set($bif_scope_)/POTENTIAL)"/>
	
	<xsl:if test="(($is_focused_bus_ + $on_focused_bus_ + $of_focused_bstd_) &gt; 0)">
	
		<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING MODULE ON BUS <xsl:value-of select="@INSTANCE"/></xsl:message></xsl:if>
		
		<xsl:choose>
			<!--  TREE VIEW -->	
	 		<xsl:when test="$G_ROOT/SAV/@MODE = 'TREE'">		
				<xsl:element name="SET">
					<xsl:attribute name="ID"><xsl:value-of select="@INSTANCE"/></xsl:attribute>
					<xsl:attribute name="CLASS">MODULE</xsl:attribute>
					
					<xsl:if test="($is_focused_bus_ &gt; 0)">
						<xsl:attribute name="RGB_BG"><xsl:value-of select="$COL_FOCUSED_MASTER"/></xsl:attribute>
					</xsl:if>
								
					<xsl:choose>
					
						<xsl:when test="(($is_focused_bus_ + $on_focused_bus_) &gt; 0)">
							<xsl:attribute name="CONNECTED_INDEX"><xsl:value-of select="@MHS_INDEX"/></xsl:attribute>
						</xsl:when>
						<xsl:otherwise>
							<xsl:attribute name="POTENTIAL_INDEX"><xsl:value-of select="@MHS_INDEX"/></xsl:attribute>
						</xsl:otherwise>
					</xsl:choose>						


		 			
					<!-- CR452579 Can only modify INSTANCE name in Hierarchal view. -->	
			  	    <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Name"       NAME="INSTANCE"  VALUE="{@INSTANCE}"/>
				    <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{@MODTYPE}" VIEWICON="{LICENSEINFO/@ICON_NAME}"/>
				    <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{@HWVERSION}"/>
				    
				    <xsl:variable name="ipClassification_">
				   		<xsl:call-template name="F_ModClass_To_IpClassification">
							<xsl:with-param name="iModClass"  select="@MODCLASS"/>
							<xsl:with-param name="iBusStd"    select="@BUSSTD"/> 
						</xsl:call-template>	
				    </xsl:variable>
				    
			       <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Classification" NAME="IPCLASS" VALUE="{$ipClassification_}"/>
			       
			       <xsl:for-each select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
						<xsl:variable name="b_bus_"      		select="@BUSNAME"/>
						<xsl:variable name="b_bstd_"      		select="@BUSSTD"/>
						<xsl:variable name="b_on_focused_bus_"  select="count($G_ROOT/SAV/BUS[(@INSTANCE = $b_bus_)])"/>
						<xsl:variable name="b_of_focused_bstd_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD   = $b_bstd_])"/>
						<xsl:variable name="bif_col_">
							<xsl:choose>
								<xsl:when test="(not($b_bus_ ='__NOC__') and ($b_on_focused_bus_  = 0) and ($b_of_focused_bstd_ &gt; 0))"><xsl:value-of select="$COL_BG_OUTOF_FOCUS_CONNECTIONS"/></xsl:when>
								<xsl:otherwise>__NONE__</xsl:otherwise>
							</xsl:choose>
						</xsl:variable>
						<xsl:if test="(($b_on_focused_bus_  + $b_of_focused_bstd_) &gt; 0)">
							<xsl:if test="$G_ROOT/SAV/@MODE = 'TREE'">
								<xsl:call-template name="WRITE_VIEW_BIF_TREE_SET">
									<xsl:with-param name="iModRef" select="../.."/>
									<xsl:with-param name="iBifRef" select="self::node()"/>
									<xsl:with-param name="iBifCol" select="$bif_col_"/>
								</xsl:call-template>	
							</xsl:if>
							<xsl:if test="$G_ROOT/SAV/@MODE = 'FLAT'">
								<xsl:call-template name="WRITE_VIEW_BIF_FLAT_SET">
									<xsl:with-param name="iModRef" select="../.."/>
									<xsl:with-param name="iBifRef" select="self::node()"/>
									<xsl:with-param name="iBifCol" select="$bif_col_"/>
								</xsl:call-template>
							</xsl:if>
						</xsl:if>
					</xsl:for-each>
				</xsl:element>
 			</xsl:when>
 			
 			<!--  FLAT VIEW -->	
 			<xsl:otherwise>
			       <xsl:for-each select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
						<xsl:variable name="b_bus_"      		select="@BUSNAME"/>
						<xsl:variable name="b_on_focused_bus_"  select="count($G_ROOT/SAV/BUS[(@INSTANCE = $b_bus_)])"/>
						<xsl:if test="($b_on_focused_bus_ &gt; 0)">
							<xsl:if test="$G_ROOT/SAV/@MODE = 'TREE'">
								<xsl:call-template name="WRITE_VIEW_BIF_TREE_SET">
									<xsl:with-param name="iModRef" select="../.."/>
									<xsl:with-param name="iBifRef" select="self::node()"/>
								</xsl:call-template>	
							</xsl:if>
							<xsl:if test="$G_ROOT/SAV/@MODE = 'FLAT'">
								<xsl:call-template name="WRITE_VIEW_BIF_FLAT_SET">
									<xsl:with-param name="iModRef" select="../.."/>
									<xsl:with-param name="iBifRef" select="self::node()"/>
								</xsl:call-template>
							</xsl:if>
						</xsl:if>
					</xsl:for-each>      	   
 			</xsl:otherwise>
 		</xsl:choose>
	</xsl:if>
	
</xsl:template>

<!--
    ===================================================
    	THE MODULE TEMPLATE FOR CONNECTED MODULES
    	IN BIF VIEW PROC FOCUS
    ===================================================
-->

<xsl:template match="MODULE" mode="_bif_view_focusing_on_connected">

	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>EXAMINING CONNECTED MODULE <xsl:value-of select="@INSTANCE"/></xsl:message></xsl:if>
	
	<xsl:variable name="m_instance_" select="@INSTANCE"/>
	<xsl:variable name="m_class_"    select="@MODCLASS"/>
	
	<xsl:variable name="bif_scope_">
		<xsl:for-each select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
			<xsl:variable name="b_std_"  select="@BUSSTD"/>
			<xsl:variable name="b_bus_"  select="@BUSNAME"/>
			<xsl:variable name="b_name_" select="@NAME"/>
	
			<xsl:choose>
				<xsl:when test="($b_bus_ = '__NOC__')"><POTENTIAL/></xsl:when>
				
				<xsl:when test="((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR')) and (count(key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]) &gt; 0)">
				
					 <xsl:variable name="p2p_scope_">
						<xsl:for-each select="$G_SYS_MODS">						
						 	<xsl:for-each select="key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]">
								<xsl:variable name="b_instance_" select="../../@INSTANCE"/>
								<xsl:variable name="b_modclass_" select="../../@MODCLASS"/>
								<xsl:variable name="b_bifname_"  select="@NAME"/>
								<xsl:if test="not(($b_bifname_ = $b_name_) and ($b_instance_ = $m_instance_))">
									<xsl:variable name="num_mast_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_])"/>
									<xsl:variable name="num_peri_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $b_instance_)])"/>
									<xsl:if test="(($num_mast_connections_  + $num_peri_connections_) &gt; 0)"><INSCOPE/></xsl:if>
									<xsl:if test="(($num_mast_connections_  + $num_peri_connections_) = 0) and not($m_class_ = 'MEMORY') and not($m_class_ = 'MEMORY_CNTLR')"><UNFOCUSED/></xsl:if>
								</xsl:if>
						 	</xsl:for-each>
					 	</xsl:for-each>
					 </xsl:variable>
					 <xsl:variable name="num_p2p_inscope_"   select="count(exsl:node-set($p2p_scope_)/INSCOPE)"/>
					 <xsl:variable name="num_p2p_unfocused_" select="count(exsl:node-set($p2p_scope_)/UNFOCUSED)"/>
					 <xsl:if test="$num_p2p_inscope_   &gt; 0"><CONNECTED/></xsl:if>
					 <xsl:if test="$num_p2p_unfocused_ &gt; 0"><UNFOCUSED/></xsl:if>
				</xsl:when>
				
					 <!-- 
	 				 <xsl:if test="$G_DEBUG='TRUE'"><xsl:message>	P2P <xsl:value-of select="$b_instance_"/> == <xsl:value-of select="$num_peri_connections_"/> UNFOCUSED</xsl:message></xsl:if>
					 <xsl:if test="$G_DEBUG='TRUE'"><xsl:message>	P2P <xsl:value-of select="$m_instance_"/>.<xsl:value-of select="$b_name_"/> = <xsl:value-of select="$num_p2p_unfocused_"/> UNFOCUSED</xsl:message></xsl:if>
					  -->
				
				<xsl:when test="((@TYPE = 'SLAVE') and not(MASTERS/MASTER)) or (@TYPE = 'MASTER')">
					<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><CONNECTED/></xsl:if>
					<xsl:if test="($b_bus_ = '__NOC__') and count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD = $b_std_]) &gt; 0"><POTENTIAL/></xsl:if>
				</xsl:when>
				
				<xsl:when test="(MASTERS/MASTER)">
					<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><POTENTIAL/></xsl:if>
					<xsl:for-each select="MASTERS/MASTER">
						<xsl:variable name="m_inst_" select="@INSTANCE"/>
						<xsl:choose>
							<xsl:when test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
							<xsl:when test="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
							<xsl:otherwise><UNFOCUSED/></xsl:otherwise>
						</xsl:choose>
					</xsl:for-each>
				</xsl:when>
			</xsl:choose>
		</xsl:for-each>
		
		<xsl:if test="$m_class_ = 'BUS'">
			<xsl:variable name="num_bifs_on_bus_" select="count(key('G_MAP_ALL_BIFS_BY_BUS',$m_instance_))"/>
			<!--  <xsl:if test="$G_DEBUG='TRUE'"><xsl:message>BBBBBB <xsl:value-of select="$m_instance_"/> has <xsl:value-of select="$num_bifs_on_bus_"/> bifs </xsl:message></xsl:if> -->
			<xsl:for-each select="key('G_MAP_ALL_BIFS_BY_BUS',$m_instance_)">
				<xsl:variable name="b_name_" select="@NAME"/>
				<xsl:variable name="b_type_" select="@TYPE"/>
				<xsl:variable name="b_inst_" select="../../@INSTANCE"/>
				<xsl:variable name="b_icls_" select="../../@MODCLASS"/>
				<xsl:variable name="is_mast_in_focus_" select="count($G_ROOT/SAV/MASTER[(@INSTANCE = $b_inst_)])"/>
				<xsl:variable name="is_peri_in_focus_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[@NAME   = $b_inst_])"/>
				<xsl:if test="(($is_peri_in_focus_ + $is_mast_in_focus_) = 0)"><UNFOCUSED/></xsl:if>
			</xsl:for-each>
		</xsl:if>
	</xsl:variable>
	
    <xsl:variable name="mod_id_" 			 select="@INSTANCE"/>	
    <xsl:variable name="potential_masts_id_" select="concat('__GROUP_MASTER__.',@INSTANCE)"/>	
	<xsl:variable name="is_master_"          select="count($G_GROUPS/BLOCK[(@ID = $potential_masts_id_)])"/>	
	<xsl:variable name="is_focused_on_"      select="count($G_ROOT/SAV/MASTER[(@INSTANCE = $mod_id_)])"/>	
	<xsl:variable name="is_peripheral_"      select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[@NAME   = $mod_id_])"/>		
	<xsl:variable name="num_potential_bifs_" select="count(exsl:node-set($bif_scope_)/POTENTIAL)"/>	
	<xsl:variable name="num_connected_bifs_" select="count(exsl:node-set($bif_scope_)/CONNECTED)"/>
	<xsl:variable name="num_unfocused_bifs_" select="count(exsl:node-set($bif_scope_)/UNFOCUSED)"/>
	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  CONNECTED BIFS <xsl:value-of select="$num_connected_bifs_"/></xsl:message></xsl:if>
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  POTENTIAL BIFS <xsl:value-of select="$num_potential_bifs_"/></xsl:message></xsl:if>
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  IS PERIPHERAL  <xsl:value-of select="$is_peripheral_"/></xsl:message></xsl:if>			
	<xsl:if test="((@MODCLASS = 'BUS') or ($num_connected_bifs_ + $is_focused_on_ + $num_potential_bifs_ + $is_peripheral_) &gt; 0)">		
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>    PLACING MODULE <xsl:value-of select="@INSTANCE"/></xsl:message></xsl:if>

		<xsl:choose>
	 		<xsl:when test="$G_ROOT/SAV/@MODE = 'TREE'">
				<xsl:element name="SET">
					<xsl:attribute name="ID"><xsl:value-of select="@INSTANCE"/></xsl:attribute>
					<xsl:attribute name="CLASS">MODULE</xsl:attribute>
					
					<xsl:choose>
						<xsl:when test="((@MODCLASS = 'BUS') or (($num_connected_bifs_ + $is_peripheral_ + $is_focused_on_) &gt; 0))">
								<xsl:attribute name="CONNECTED_INDEX"><xsl:value-of select="@MHS_INDEX"/></xsl:attribute>
						</xsl:when>
						<xsl:otherwise>
								<xsl:attribute name="POTENTIAL_INDEX"><xsl:value-of select="@MHS_INDEX"/></xsl:attribute>
						</xsl:otherwise>
		 			</xsl:choose>
		 			
		 			
					<xsl:choose>
						<xsl:when test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $mod_id_)]) &gt; 0">
							<xsl:attribute name="RGB_BG"><xsl:value-of select="$COL_FOCUSED_MASTER"/></xsl:attribute>
						</xsl:when>
						<xsl:when test="$num_unfocused_bifs_ &gt; 0">
							<xsl:attribute name="RGB_FG"><xsl:value-of select="$COL_BG_OUTOF_FOCUS_CONNECTIONS"/></xsl:attribute>
						</xsl:when>
					</xsl:choose>
						<!--		
							   CR452579
							   Can only modify INSTANCE name in Hierarchal view.
						-->	
				  	    <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Name"       NAME="INSTANCE"  VALUE="{@INSTANCE}"/>
					    <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{@MODTYPE}" VIEWICON="{LICENSEINFO/@ICON_NAME}"/>
					    <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{@HWVERSION}"/>
					    
					    <xsl:variable name="ipClassification_">
					   		<xsl:call-template name="F_ModClass_To_IpClassification">
								<xsl:with-param name="iModClass"  select="@MODCLASS"/>
								<xsl:with-param name="iBusStd"    select="@BUSSTD"/> 
							</xsl:call-template>	
					    </xsl:variable>
				       <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Classification" NAME="IPCLASS" VALUE="{$ipClassification_}"/>
				       
			      	   <xsl:apply-templates  select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]" mode="_bif_view_focusing_on_connected"/>
				</xsl:element>
	 		</xsl:when>
	 		
	 		<xsl:otherwise>
	      	   <xsl:apply-templates  select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]" mode="_bif_view_focusing_on_connected"/>
	 		</xsl:otherwise>
		</xsl:choose>
	</xsl:if>
</xsl:template>


<!--
    ===================================================
    	THE MODULE TEMPLATE FOR POTENTIAL MODULES
    	IN BIF VIEW PROC FOCUS
    ===================================================
-->

<xsl:template match="MODULE" mode="_bif_view_focusing_on_potentials">

	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>EXAMINING POTENTIAL MODULE <xsl:value-of select="@INSTANCE"/></xsl:message></xsl:if>
	
	<xsl:variable name="m_instance_" select="@INSTANCE"/>
	<xsl:variable name="m_modclass_" select="@MODCLASS"/>
	
	<xsl:variable name="bif_scope_">
		<xsl:for-each select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
			<xsl:variable name="b_std_"  select="@BUSSTD"/>
			<xsl:variable name="b_bus_"  select="@BUSNAME"/>
			<xsl:choose>
			
				<xsl:when test="($b_bus_ = '__NOC__')"><POTENTIAL/></xsl:when>
				
				<xsl:when test="((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR')) and (count(key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]) &gt; 0)">
					 <xsl:variable name="p2p_scope_">
						<xsl:for-each select="$G_SYS_MODS"> <!-- To set the right scope for the keys  -->
						 	<xsl:for-each select="key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]">
								<xsl:variable name="b_instance_" select="../../@INSTANCE"/>
								<xsl:variable name="b_modclass_" select="../../@MODCLASS"/>
								<xsl:variable name="num_mast_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_])"/>
								<xsl:variable name="num_peri_connections_">
									<xsl:choose>
										<xsl:when test="((($m_modclass_ = 'PROCESSOR') and ($b_modclass_ = 'PROCESSOR')) or not($b_modclass_ = 'PROCESSOR'))">
								 			<xsl:value-of select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $b_instance_)])"/>
										</xsl:when>
										<xsl:otherwise>0</xsl:otherwise>
									</xsl:choose>
								</xsl:variable>	
									
								<xsl:if test="(($num_mast_connections_  + $num_peri_connections_) &gt; 0)"><INSCOPE/></xsl:if>
								<xsl:if test="(($num_mast_connections_  + $num_peri_connections_) = 0) and not($m_modclass_ = 'MEMORY') and not($m_modclass_ = 'MEMORY_CNTLR')"><UNFOCUSED/></xsl:if>
						 	</xsl:for-each>
					 	</xsl:for-each>
					 </xsl:variable>
					 <xsl:variable name="num_p2p_inscope_"   select="count(exsl:node-set($p2p_scope_)/INSCOPE)"/>
					 <xsl:variable name="num_p2p_unfocused_" select="count(exsl:node-set($p2p_scope_)/UNFOCUSED)"/>
					 <xsl:if test="$num_p2p_inscope_   &gt; 0"><CONNECTED/></xsl:if>
					 <xsl:if test="$num_p2p_unfocused_ &gt; 0"><UNFOCUSED/></xsl:if>
				</xsl:when>
				
				<xsl:when test="(@TYPE = 'SLAVE') and not(MASTERS/MASTER)">
					<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><CONNECTED/></xsl:if>
					<xsl:if test="($b_bus_ = '__NOC__') and count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD = $b_std_]) &gt; 0"><POTENTIAL/></xsl:if>
				</xsl:when>
				
				<xsl:when test="(MASTERS/MASTER)">
					<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><POTENTIAL/></xsl:if>
					<xsl:for-each select="MASTERS/MASTER">
						<xsl:variable name="m_inst_" select="@INSTANCE"/>
						<xsl:choose>
							<xsl:when test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
							<xsl:when test="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
							<xsl:otherwise><UNFOCUSED/></xsl:otherwise>
						</xsl:choose>
					</xsl:for-each>
				</xsl:when>
			</xsl:choose>
		</xsl:for-each>
		
		<xsl:if test="$m_modclass_ = 'BUS'">
			<xsl:variable name="num_bifs_on_bus_" select="count(key('G_MAP_ALL_BIFS_BY_BUS',$m_instance_))"/>
			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>BUS <xsl:value-of select="$m_instance_"/> has <xsl:value-of select="$num_bifs_on_bus_"/> bifs </xsl:message></xsl:if>
			<xsl:for-each select="key('G_MAP_ALL_BIFS_BY_BUS',$m_instance_)">
				<xsl:variable name="b_name_" select="@NAME"/>
				<xsl:variable name="b_type_" select="@TYPE"/>
				<xsl:variable name="b_inst_" select="../../@INSTANCE"/>
				<xsl:variable name="b_icls_" select="../../@MODCLASS"/>
				<xsl:variable name="is_mast_in_focus_" select="count($G_ROOT/SAV/MASTER[(@INSTANCE = $b_inst_)])"/>
				<xsl:variable name="is_peri_in_focus_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[@NAME   = $b_inst_])"/>
				<xsl:if test="(($is_peri_in_focus_ + $is_mast_in_focus_) = 0)"><UNFOCUSED/></xsl:if>				
			</xsl:for-each>
		</xsl:if>
	</xsl:variable>
	
    <xsl:variable name="mod_id_" 			 select="@INSTANCE"/>	
    <xsl:variable name="potential_masts_id_" select="concat('__GROUP_MASTER__.',@INSTANCE)"/>	
	<xsl:variable name="is_master_"          select="count($G_GROUPS/BLOCK[(@ID = $potential_masts_id_)])"/>	
	<xsl:variable name="is_peripheral_"      select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[@NAME   = $mod_id_])"/>		
	<xsl:variable name="num_potential_bifs_" select="count(exsl:node-set($bif_scope_)/POTENTIAL)"/>	
	<xsl:variable name="num_connected_bifs_" select="count(exsl:node-set($bif_scope_)/CONNECTED)"/>
	<xsl:variable name="num_unfocused_bifs_" select="count(exsl:node-set($bif_scope_)/UNFOCUSED)"/>
<!-- 
-->
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  <xsl:value-of select="$num_connected_bifs_"/> connected BIFS</xsl:message></xsl:if>	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  <xsl:value-of select="$num_potential_bifs_"/> potential bifs </xsl:message></xsl:if>	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  <xsl:value-of select="$num_unfocused_bifs_"/> unfocused bifs </xsl:message></xsl:if>	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  <xsl:value-of select="$is_peripheral_"/> is a peripheral</xsl:message></xsl:if>	
	
	<xsl:if test="(($num_connected_bifs_ + $num_potential_bifs_ + $is_peripheral_) &gt; 0)">
		<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING POTENTIAL MODULE <xsl:value-of select="@INSTANCE"/></xsl:message></xsl:if>
		<xsl:choose>
		
	 		<xsl:when test="$G_ROOT/SAV/@MODE = 'TREE'">		
				<xsl:element name="SET">
					<xsl:attribute name="ID"><xsl:value-of select="@INSTANCE"/></xsl:attribute>
					<xsl:attribute name="CLASS">MODULE</xsl:attribute>
					<xsl:choose>
						<xsl:when  test="(($is_peripheral_ &gt; 0) or ($num_connected_bifs_ &gt; 0))">
							<xsl:attribute name="CONNECTED_INDEX"><xsl:value-of select="@MHS_INDEX"/></xsl:attribute>
						</xsl:when>
						<xsl:otherwise>
							<xsl:attribute name="POTENTIAL_INDEX"><xsl:value-of select="@MHS_INDEX"/></xsl:attribute>
						</xsl:otherwise>
					</xsl:choose>
					
					<xsl:choose>
						<xsl:when test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $mod_id_)]) &gt; 0">
							<xsl:attribute name="RGB_BG"><xsl:value-of select="$COL_FOCUSED_MASTER"/></xsl:attribute>
						</xsl:when>
						<xsl:when test="$num_unfocused_bifs_ &gt; 0">
							<xsl:attribute name="RGB_FG"><xsl:value-of select="$COL_BG_OUTOF_FOCUS_CONNECTIONS"/></xsl:attribute>
						</xsl:when>
					</xsl:choose>		
					
					<!-- CR452579 Can only modify INSTANCE name in Hierarchal view. -->	
			  	    <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Name"       NAME="INSTANCE"  VALUE="{@INSTANCE}"/>
				    <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{@MODTYPE}" VIEWICON="{LICENSEINFO/@ICON_NAME}"/>
				    <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{@HWVERSION}"/>
				    
				    <xsl:variable name="ipClassification_">
				   		<xsl:call-template name="F_ModClass_To_IpClassification">
							<xsl:with-param name="iModClass"  select="@MODCLASS"/>
							<xsl:with-param name="iBusStd"    select="@BUSSTD"/> 
						</xsl:call-template>	
				    </xsl:variable>
				    
			       <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Classification" NAME="IPCLASS" VALUE="{$ipClassification_}"/>
			       
		      	   <xsl:apply-templates  select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]" mode="_bif_view_focusing_on_potentials"/>
				</xsl:element>		       
 			</xsl:when>
 			
 			<xsl:otherwise>
		      	   <xsl:apply-templates  select="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]" mode="_bif_view_focusing_on_potentials"/>
 			</xsl:otherwise>
 		</xsl:choose>
	</xsl:if>
</xsl:template>

<!--
    +++++++++++++++++++++++++++++++++++++++++++++++++++++
    		       BUS INTERFACE TEMPLATES
    +++++++++++++++++++++++++++++++++++++++++++++++++++++
-->

<!--
    ===================================================
    	THE BIF TEMPLATE FOR CONNECTED MODULES
    	IN BIF VIEW PROC FOCUS
    ===================================================
-->
<xsl:template match="BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]" mode="_bif_view_focusing_on_connected">
	<xsl:variable name="m_instance_" select="../../@INSTANCE"/>
	<xsl:variable name="b_std_"      select="@BUSSTD"/>
	<xsl:variable name="b_bus_"      select="@BUSNAME"/>
	<xsl:variable name="b_name_"     select="@NAME"/>
	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message> EXAMINING CONNECTED INTERFACE <xsl:value-of select="$m_instance_"/>.<xsl:value-of select="$b_name_"/></xsl:message></xsl:if>
	
	<xsl:variable name="bif_scope_">
		<xsl:choose>
			<xsl:when test="($b_bus_ = '__NOC__')"><POTENTIAL/></xsl:when>
			<xsl:when test="((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR')) and (count(key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]) &gt; 0)">
				 <xsl:variable name="p2p_scope_">
					<xsl:for-each select="$G_SYS_MODS">	<!--  to put in right scope for key below -->
					 	<xsl:for-each select="key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]">
							<xsl:variable name="p2p_bifname_"  select="@NAME"/>
							<xsl:variable name="p2p_instance_" select="../../@INSTANCE"/>
							
							<xsl:variable name="num_proc_connections_" select="count(key('G_MAP_PROCESSORS',$p2p_instance_))"/>
							<xsl:variable name="num_mast_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_])"/>
							<xsl:variable name="num_peri_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $p2p_instance_)])"/>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  <xsl:value-of select="$p2p_instance_"/>.<xsl:value-of select="$p2p_bifname_"/></xsl:message></xsl:if>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  PROC CONNECTIONS <xsl:value-of select="$num_proc_connections_"/></xsl:message></xsl:if>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  MAST CONNECTIONS <xsl:value-of select="$num_mast_connections_"/></xsl:message></xsl:if>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  PERI CONNECTIONS <xsl:value-of select="$num_peri_connections_"/></xsl:message></xsl:if>
							
							<xsl:if test="($num_mast_connections_ = 0)   and ($num_proc_connections_ &gt; 0)"><OUTSCOPE/></xsl:if>
							<xsl:if test="($num_mast_connections_ &gt; 0) or ($num_peri_connections_ &gt; 0)"><INSCOPE/></xsl:if>
							
					 	</xsl:for-each>
				 	</xsl:for-each>
				 </xsl:variable>
				 
				 <xsl:variable name="num_p2p_inscope_"  select="count(exsl:node-set($p2p_scope_)/INSCOPE)"/>
				 <xsl:variable name="num_p2p_outscope_" select="count(exsl:node-set($p2p_scope_)/OUTSCOPE)"/>
				 
				 <xsl:if test="(($num_p2p_inscope_ &gt; 0) and ($num_p2p_outscope_ = 0))"><CONNECTED/></xsl:if>
			</xsl:when>
			<xsl:when test="(@TYPE = 'MASTER')">
				<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><CONNECTED/></xsl:if>
			</xsl:when>
			<xsl:when test="(@TYPE = 'SLAVE') and not(MASTERS/MASTER)">
				<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><CONNECTED/></xsl:if>
				<xsl:if test="($b_bus_ = '__NOC__') and count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD = $b_std_]) &gt; 0"><POTENTIAL/></xsl:if>
			</xsl:when>
			<xsl:when test="(MASTERS/MASTER)">
				<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><POTENTIAL/></xsl:if>
				<xsl:for-each select="MASTERS/MASTER">
					<xsl:variable name="m_inst_" select="@INSTANCE"/>
					<xsl:choose>
						<xsl:when test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
						<xsl:when test="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
						<xsl:otherwise><UNFOCUSED/></xsl:otherwise>
					</xsl:choose>
				</xsl:for-each>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>		
 	
	<xsl:variable name="num_scope_unfocuseds_" select="count(exsl:node-set($bif_scope_)/UNFOCUSED)"/> 	
	<xsl:variable name="num_scope_potentials_" select="count(exsl:node-set($bif_scope_)/POTENTIAL)"/>
	<xsl:variable name="num_scope_connecteds_" select="count(exsl:node-set($bif_scope_)/CONNECTED)"/>
	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  CONNECTED SCOPE <xsl:value-of select="$num_scope_connecteds_"/></xsl:message></xsl:if>
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  POTENTIAL SCOPE <xsl:value-of select="$num_scope_potentials_"/></xsl:message></xsl:if>

	<xsl:variable name="include_bif_">
		<xsl:choose>
			<xsl:when test="($b_bus_ = '__NOC__')">TRUE</xsl:when>
			<xsl:when test="(((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR')) and ($num_scope_connecteds_  &gt; 0))">TRUE</xsl:when>
			<xsl:when test="((@TYPE = 'MASTER') or (@TYPE = 'SLAVE') or (@TYPE = 'MASTER_SLAVE')) and (($num_scope_potentials_  &gt; 0) or ($num_scope_connecteds_  &gt; 0))">TRUE</xsl:when>
			<xsl:otherwise>FALSE</xsl:otherwise>
		</xsl:choose>			
	</xsl:variable>
				
 	<xsl:if test="($include_bif_ = 'TRUE')">
		<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>   PLACING CONNECTED INTERFACE <xsl:value-of select="$m_instance_"/>.<xsl:value-of select="$b_name_"/></xsl:message></xsl:if>

 		<xsl:variable name="bif_col_">
			<xsl:choose>
				<xsl:when test="($num_scope_unfocuseds_ &gt; 0)"><xsl:value-of select="$COL_BG_OUTOF_FOCUS_CONNECTIONS"/></xsl:when>
				<xsl:otherwise>__NONE__</xsl:otherwise>
			</xsl:choose>	
 		</xsl:variable>	
		
 		<xsl:if test="$G_ROOT/SAV/@MODE = 'TREE'">
			<xsl:call-template name="WRITE_VIEW_BIF_TREE_SET">
				<xsl:with-param name="iModRef" select="../.."/>
				<xsl:with-param name="iBifRef" select="self::node()"/>
				<xsl:with-param name="iBifCol" select="$bif_col_"/>
			</xsl:call-template>	
		</xsl:if>		
		
		<xsl:if test="$G_ROOT/SAV/@MODE = 'FLAT'">
			<xsl:call-template name="WRITE_VIEW_BIF_FLAT_SET">
				<xsl:with-param name="iModRef" select="../.."/>
				<xsl:with-param name="iBifRef" select="self::node()"/>
				<xsl:with-param name="iBifCol" select="$bif_col_"/>
			</xsl:call-template>
		</xsl:if>	
  	</xsl:if>
</xsl:template>  

<!--
    ===================================================
    	THE BIF TEMPLATE FOR POTENTIAL MODULES
    	IN BIF VIEW PROC FOCUS
    ===================================================
-->

<xsl:template match="BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]" mode="_bif_view_focusing_on_potentials">
	<xsl:variable name="m_instance_" select="../../@INSTANCE"/>
	<xsl:variable name="b_name_"  	 select="@NAME"/>
	<xsl:variable name="b_std_"  	 select="@BUSSTD"/>
	<xsl:variable name="b_bus_"      select="@BUSNAME"/>
	
	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message> EXAMINING POTENTIAL INTERFACE <xsl:value-of select="$m_instance_"/>.<xsl:value-of select="$b_name_"/></xsl:message></xsl:if>
	
	<xsl:variable name="bif_scope_">
		<xsl:choose>
			<xsl:when test="($b_bus_ = '__NOC__')"><POTENTIAL/></xsl:when>
			
			<xsl:when test="((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR')) and (count(key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]) &gt; 0)">
				 <xsl:variable name="p2p_scope_">
					<xsl:for-each select="$G_SYS_MODS">						
					 	<xsl:for-each select="key('G_MAP_P2P_BIFS',$b_bus_)[not(@BUSNAME  = '__NOC__')]">
							<xsl:variable name="b_instance_" select="../../@INSTANCE"/>
							
							<xsl:variable name="num_proc_connections_" select="count(key('G_MAP_PROCESSORS',$b_instance_))"/>
							<xsl:variable name="num_mast_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_])"/>
							<xsl:variable name="num_peri_connections_" select="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $b_instance_)])"/>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  PROC CONNECTIONS <xsl:value-of select="$num_proc_connections_"/></xsl:message></xsl:if>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  MAST CONNECTIONS <xsl:value-of select="$num_mast_connections_"/></xsl:message></xsl:if>
							<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>  PERI CONNECTIONS <xsl:value-of select="$num_peri_connections_"/></xsl:message></xsl:if>
							
							<xsl:if test="($num_mast_connections_ = 0)   and ($num_proc_connections_ &gt; 0)"><OUTSCOPE/></xsl:if>
							<xsl:if test="($num_mast_connections_ &gt; 0) or ($num_peri_connections_ &gt; 0)"><INSCOPE/></xsl:if>
							
					 	</xsl:for-each>
				 	</xsl:for-each>
				 </xsl:variable>
				 
				 <xsl:variable name="num_p2p_inscope_"  select="count(exsl:node-set($p2p_scope_)/INSCOPE)"/>
				 <xsl:variable name="num_p2p_outscope_" select="count(exsl:node-set($p2p_scope_)/OUTSCOPE)"/>
				 
				 <xsl:if test="(($num_p2p_inscope_ &gt; 0) and ($num_p2p_outscope_ = 0))"><CONNECTED/></xsl:if>
			</xsl:when>	
			<xsl:when test="(((@TYPE = 'SLAVE') and not(MASTERS/MASTER)) or (@TYPE = 'MASTER'))">
				<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><CONNECTED/></xsl:if>
				<xsl:if test="($b_bus_ = '__NOC__') and count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@BUSSTD = $b_std_]) &gt; 0"><POTENTIAL/></xsl:if>
			</xsl:when>
			<xsl:when test="(MASTERS/MASTER)">
				<xsl:if test="count(exsl:node-set($G_FOCUSED_SCOPE)/BUS[@NAME   = $b_bus_]) &gt; 0"><POTENTIAL/></xsl:if>
				<xsl:for-each select="MASTERS/MASTER">
					<xsl:variable name="m_inst_" select="@INSTANCE"/>
					<xsl:choose>
						<xsl:when test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
						<xsl:when test="count(exsl:node-set($G_FOCUSED_SCOPE)/PERIPHERAL[(@NAME   = $m_inst_)]) &gt; 0"><CONNECTED/></xsl:when>
						<xsl:otherwise><UNFOCUSED/></xsl:otherwise>
					</xsl:choose>
				</xsl:for-each>
			</xsl:when>
		</xsl:choose>
	</xsl:variable>		
 	
	<xsl:variable name="num_scope_potentials_" select="count(exsl:node-set($bif_scope_)/POTENTIAL)"/>
	<xsl:variable name="num_scope_connecteds_" select="count(exsl:node-set($bif_scope_)/CONNECTED)"/>
	<xsl:variable name="num_scope_unfocuseds_" select="count(exsl:node-set($bif_scope_)/UNFOCUSED)"/>	
	
	<xsl:variable name="include_bif_">
		<xsl:choose>
			<xsl:when test="($b_bus_ = '__NOC__')">TRUE</xsl:when>
			<xsl:when test="(((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR')) and ($num_scope_connecteds_  &gt; 0))">TRUE</xsl:when>
			<xsl:when test="((@TYPE = 'MASTER') or (@TYPE = 'SLAVE') or (@TYPE = 'MASTER_SLAVE')) and (($num_scope_potentials_  &gt; 0) or ($num_scope_connecteds_  &gt; 0))">TRUE</xsl:when>
			<xsl:otherwise>FALSE</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>

	<xsl:variable name="bif_col_">
		<xsl:choose>
			<xsl:when test="($num_scope_unfocuseds_ &gt; 0)"><xsl:value-of select="$COL_BG_OUTOF_FOCUS_CONNECTIONS"/></xsl:when>
			<xsl:otherwise>__NONE__</xsl:otherwise>
		</xsl:choose>	
	</xsl:variable>
	
	<xsl:if test="($include_bif_ = 'TRUE')">
		<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>   PLACING POTENTIAL INTERFACE <xsl:value-of select="$m_instance_"/>.<xsl:value-of select="$b_name_"/></xsl:message></xsl:if>
		<xsl:if test="$G_ROOT/SAV/@MODE = 'TREE'">
			<xsl:call-template name="WRITE_VIEW_BIF_TREE_SET">
				<xsl:with-param name="iModRef" select="../.."/>
				<xsl:with-param name="iBifRef" select="self::node()"/>
				<xsl:with-param name="iBifCol" select="$bif_col_"/>
			</xsl:call-template>	
		</xsl:if>
		<xsl:if test="$G_ROOT/SAV/@MODE = 'FLAT'">
			<xsl:call-template name="WRITE_VIEW_BIF_FLAT_SET">
				<xsl:with-param name="iModRef" select="../.."/>
				<xsl:with-param name="iBifRef" select="self::node()"/>
				<xsl:with-param name="iBifCol" select="$bif_col_"/>
			</xsl:call-template>
		</xsl:if>	
	</xsl:if>
	
</xsl:template>

<!--  THINGS TO IGNORE -->
<!-- Ignore all non valid bus interfaces -->
<xsl:template match="MODULE/DESCRIPTION" mode="_bif_view_focusing_on_potentials">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/PARAMETERS" mode="_bif_view_focusing_on_potentials">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/DOCUMENTATION" mode="_bif_view_focusing_on_potentials">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/LICENSEINFO" mode="_bif_view_focusing_on_potentials">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<!-- Ignore all non valid bus interfaces -->
<xsl:template match="BUSINTERFACES/BUSINTERFACE[(@IS_VALID = 'FALSE')]" mode="_bif_view_focusing_on_potentials">
</xsl:template>

<xsl:template match="MODULE/DESCRIPTION" mode="_bif_view_focusing_on_connected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/PARAMETERS" mode="_bif_view_focusing_on_connected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/DOCUMENTATION" mode="_bif_view_focusing_on_connected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/LICENSEINFO" mode="_bif_view_focusing_on_connected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="BUSINTERFACES/BUSINTERFACE[(@IS_VALID = 'FALSE')]" mode="_bif_view_focusing_on_connected">
</xsl:template>

<!-- Ignore all non valid bus interfaces -->
<xsl:template match="SAV" mode="_port_view_focusing_on_selected">
</xsl:template>

<xsl:template match="MODULE/DESCRIPTION" mode="_port_view_focusing_on_selected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/PARAMETERS" mode="_port_view_focusing_on_selected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/DOCUMENTATION" mode="_port_view_focusing_on_selected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<xsl:template match="MODULE/LICENSEINFO" mode="_port_view_focusing_on_selected">
<!--  <xsl:message>Ignoring invalid bus interface <xsl:value-of select="@NAME"/></xsl:message> -->
</xsl:template>

<!-- Ignore all non valid bus interfaces -->
<xsl:template match="BUSINTERFACES/BUSINTERFACE[(@IS_VALID = 'FALSE')]" mode="_port_view_focusing_on_selected">
</xsl:template>

<!-- 
	Only write bus interfaces that are valid for non point to point interfaces 
	that have busstds the processor can see 
-->

<!--
    ===============================================
          GROUP VIEW TRANSFORMS
    ===============================================
-->

<xsl:template name="WRITE_VIEW_GROUPS">
    <xsl:param name="iModules"/>

    <xsl:if test="$G_DEBUG='TRUE'">
       <!--
       <xsl:message>BLKD AREA            = <xsl:value-of select="$blkd_full_w_"/> X <xsl:value-of select="$blkd_full_h_"/></xsl:message>
       <xsl:message>NUMOF BUSSTD COLORS  = <xsl:value-of select="$COL_BUSSTDS_NUMOF"/></xsl:message>
            <xsl:message>NUMOF INTERFACE TYPES= <xsl:value-of select="$G_IFTYPES_NUMOF"/></xsl:message> 
            <xsl:message>NUMOF DIRS           = <xsl:value-of select="$G_BLKD_COMPASS_DIRS_NUMOF"/></xsl:message>
        <xsl:apply-templates select="$G_BLOCKS/node()" mode="_place_module_blocks_"/>        
        -->
    </xsl:if>
   
    <xsl:element name="SET">
        <xsl:attribute name="CLASS">PROJECT</xsl:attribute>
        <xsl:attribute name="VIEW_ID">BUSINTERFACE</xsl:attribute>
        <xsl:attribute name="DISPLAYMODE">TREE</xsl:attribute>
    	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    		<xsl:with-param name="iModules" select="$G_BLOCKS"/>
    	</xsl:call-template>	
    </xsl:element>
</xsl:template>
<xsl:template name="WRITE_VIEW_BIF_GROUPS">
	<xsl:param name="iModules"/>
    
	<xsl:for-each select="$iModules/BLOCK[@ID and not(BLOCK) and not(@C)]">
    	<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING BUS <xsl:value-of select="@ID"/></xsl:message></xsl:if>
	
    	<xsl:variable name="m_id_" select="@ID"/>
    	<xsl:variable name="m_module_"   select="$G_SYS_MODS/MODULE[@INSTANCE = $m_id_]"/>
    	<xsl:variable name="m_instance_" select="$m_module_/@INSTANCE"/>
    	<xsl:variable name="m_version_"  select="$m_module_/@HWVERSION"/>
    	<xsl:variable name="m_type_"     select="$m_module_/@MODTYPE"/>
    	<xsl:variable name="m_class_"    select="$m_module_/@MODCLASS"/>
    	<xsl:variable name="m_busstd_"   select="$m_module_/@BUSSTD"/>
    	
	 	<xsl:element name="SET">
	        <xsl:attribute name="ID"><xsl:value-of select="@ID"/></xsl:attribute>
	        <xsl:attribute name="CLASS">MODULE</xsl:attribute>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">Name</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">TEXTBOX</xsl:attribute>
	        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
	        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_instance_"/></xsl:attribute>
	 		</xsl:element>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">IP Type</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">MODTYPE</xsl:attribute>
	        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_type_"/></xsl:attribute>
	 		</xsl:element>
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">IP Version</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">HWVERSION</xsl:attribute>
	        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_version_"/></xsl:attribute>
	 		</xsl:element>	 		
	 		<xsl:element name="VARIABLE">
	        	<xsl:attribute name="VIEWDISP">IP Classification</xsl:attribute>
	        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
	        	<xsl:attribute name="NAME">IPCLASS</xsl:attribute>
	        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_busstd_"/> BUS</xsl:attribute>
	 		</xsl:element>	 	 		
	    </xsl:element>
   </xsl:for-each> 
	    
	<xsl:for-each select="$iModules/BLOCK[@ID and BLOCK]">
		<xsl:choose>	
			<xsl:when test="not(starts-with(@ID,'__')) and BLOCK[@C] and (not(BLOCK/BLOCK) or BLOCK/BLOCK[@CP])">
			<!-- 
  				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING MODULE <xsl:value-of select="@ID"/></xsl:message></xsl:if>
			 -->
  				<xsl:variable name="m_id_"       select="@ID"/>
		    	<xsl:variable name="m_module_"   select="$G_SYS_MODS/MODULE[@INSTANCE = $m_id_]"/>
		    	<xsl:variable name="m_instance_" select="$m_module_/@INSTANCE"/>
		    	<xsl:variable name="m_type_"     select="$m_module_/@MODTYPE"/>
		    	<xsl:variable name="m_class_"    select="$m_module_/@MODCLASS"/>
		    	<xsl:variable name="m_version_"  select="$m_module_/@HWVERSION"/>
		    	
			 	<xsl:element name="SET">
			        <xsl:attribute name="ID"><xsl:value-of select="@ID"/></xsl:attribute>
			        <xsl:attribute name="CLASS">MODULE</xsl:attribute>
			        
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">Name</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">TEXTBOX</xsl:attribute>
			        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
			        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_instance_"/></xsl:attribute>
			 		</xsl:element>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">IP Type</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">MODTYPE</xsl:attribute>
			        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_type_"/></xsl:attribute>
			 		</xsl:element>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">IP Version</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">HWVERSION</xsl:attribute>
			        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_version_"/></xsl:attribute>
			 		</xsl:element>	 		
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">IP Classification</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">IPCLASS</xsl:attribute>
			        	<xsl:attribute name="VALUE"><xsl:value-of select="$m_class_"/></xsl:attribute>
			 		</xsl:element>
			 		
					<xsl:for-each select="BLOCK[@C and @ID]">
		  				<xsl:variable name="b_bus_"    select="@C"/>
		    			<xsl:variable name="b_name_"   select="@ID"/>
						<xsl:variable name="b_if_"     select="$m_module_/BUSINTERFACES/BUSINTERFACE[(@NAME = $b_name_)]"/>
		    			<xsl:variable name="b_type_"   select="$b_if_/@TYPE"/>
		    			<xsl:variable name="b_busstd_" select="$b_if_/@BUSSTD"/>
		    			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING BIF <xsl:value-of select="$b_name_"/></xsl:message></xsl:if>
		    			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>       TYPE <xsl:value-of select="$b_type_"/></xsl:message></xsl:if>
		    			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>       BUS  <xsl:value-of select="$b_bus_"/></xsl:message></xsl:if>
  				
		    			<xsl:variable name="b_busNameViewType_">
			    			<xsl:choose>
			    				<xsl:when test="$b_type_ = 'INITIATOR'">TEXTBOX</xsl:when>
								<xsl:when test="starts-with(@ID,'S_AXI')">BUTTON</xsl:when>
								<xsl:when test="starts-with(@ID,'S0_AXI')">BUTTON</xsl:when>
								<xsl:when test="starts-with(@ID,'S1_AXI')">BUTTON</xsl:when>
								<xsl:otherwise>DROPDOWN</xsl:otherwise>
			    			</xsl:choose>
		    			</xsl:variable>
		    			<xsl:variable name="b_busName_">
	                         <xsl:choose>
	                             <xsl:when test="$b_if_/MASTERS/MASTER">
	                             	<xsl:variable name="mastersList_"><xsl:for-each select="$b_if_/MASTERS/MASTER"><xsl:if test="position() &gt; 1"> &amp; </xsl:if><xsl:value-of select="concat(@INSTANCE,'.',@BUSINTERFACE)"/></xsl:for-each></xsl:variable>
	                             	<xsl:variable name="mastersConn_" select="concat($b_bus_,':',$mastersList_)"/>
	                             	 <xsl:value-of select="$mastersConn_"/>
	                          </xsl:when>
	                          <xsl:otherwise><xsl:value-of select="$b_bus_"/></xsl:otherwise>
	                         </xsl:choose> 		    			
		    			</xsl:variable>
		    			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>       VIEWTYPE <xsl:value-of select="$b_busNameViewType_"/></xsl:message></xsl:if>
		    			<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>       BUSNAME  <xsl:value-of select="$b_busName_"/></xsl:message></xsl:if>
			 			<xsl:element name="SET">
							<xsl:attribute name="ID"><xsl:value-of select="@ID"/></xsl:attribute>
					        <xsl:attribute name="CLASS">BUSINTERFACE</xsl:attribute>
					 		<xsl:element name="VARIABLE">
					        	<xsl:attribute name="VIEWDISP">NAME</xsl:attribute>
					        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
					        	<xsl:attribute name="NAME">NAME</xsl:attribute>
					        	<xsl:attribute name="VALUE"><xsl:value-of select="$b_name_"/></xsl:attribute>
					 		</xsl:element>
					 		<xsl:element name="VARIABLE">
					        	<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
					        	<xsl:attribute name="VIEWTYPE"><xsl:value-of select="$b_busNameViewType_"/></xsl:attribute>
					        	<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
					        	<xsl:attribute name="VALUE"><xsl:value-of select="$b_busName_"/></xsl:attribute>
					 		</xsl:element>
					 		<xsl:element name="VARIABLE">
					        	<xsl:attribute name="VIEWDISP">Type</xsl:attribute>
					        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
					        	<xsl:attribute name="NAME">TYPE</xsl:attribute>
					        	<xsl:attribute name="VALUE"><xsl:value-of select="$b_type_"/></xsl:attribute>
					 		</xsl:element>	 		
					 		<xsl:element name="VARIABLE">
					        	<xsl:attribute name="VIEWDISP">Bus Standard</xsl:attribute>
					        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
					        	<xsl:attribute name="NAME">BUSSTD</xsl:attribute>
					        	<xsl:attribute name="VALUE"><xsl:value-of select="$b_busstd_"/></xsl:attribute>
					 		</xsl:element>			 			
			 			</xsl:element>
					</xsl:for-each>
		 		</xsl:element>
			</xsl:when>
			
			<xsl:when test="starts-with(@ID,'__GROUP_PROCESSOR__')">
			
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PROCESSOR GROUP<xsl:value-of select="@ID"/></xsl:message></xsl:if>
  				<xsl:variable name="p_id_" select="substring-after(@ID,'__GROUP_PROCESSOR__')"/>
  				<xsl:variable name="m_id_" select="concat('PROCESSOR',$p_id_)"/>
			 	<xsl:element name="SET">
			        <xsl:attribute name="ID"><xsl:value-of select="$m_id_"/></xsl:attribute>
			        <xsl:attribute name="CLASS">GROUP</xsl:attribute>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">NAME</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
			        	<xsl:attribute name="VALUE">Subsystem of <xsl:value-of select="$p_id_"/></xsl:attribute>
			 		</xsl:element>
			 	   	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
		 		</xsl:element>	
			</xsl:when>
			
			<xsl:when test="starts-with(@ID,'__GROUP_MASTER__')">
			
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>MASTER GROUP<xsl:value-of select="@ID"/></xsl:message></xsl:if>
  				<xsl:variable name="p_id_" select="substring-after(@ID,'__GROUP_MASTER__')"/>
  				<xsl:variable name="m_id_" select="concat('MASTER',$p_id_)"/>  				
			 	<xsl:element name="SET">
			        <xsl:attribute name="ID"><xsl:value-of select="$m_id_"/></xsl:attribute>
			        <xsl:attribute name="CLASS">GROUP</xsl:attribute>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">NAME</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
			        	<xsl:attribute name="VALUE">Subsystem of <xsl:value-of select="$p_id_"/></xsl:attribute>
			 		</xsl:element>
			 	   	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
		 		</xsl:element>	
			</xsl:when>			
			
			<xsl:when test="starts-with(@ID,'__GROUP_SHARED__')">
  				<xsl:variable name="s_id_" select="substring-after(@ID,'__GROUP_SHARED__')"/>
  				<xsl:variable name="m_id_" select="concat('SHARED',$s_id_)"/>  				
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING SHARED PERIPHERALS <xsl:value-of select="$s_id_"/></xsl:message></xsl:if>
			 	<xsl:element name="SET">
			        <xsl:attribute name="ID"><xsl:value-of select="$m_id_"/></xsl:attribute>
			        <xsl:attribute name="CLASS">GROUP</xsl:attribute>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">NAME</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
			        	<xsl:attribute name="VALUE">Peripherals shared by <xsl:value-of select="$s_id_"/></xsl:attribute>
			 		</xsl:element>
			 	   	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
		 		</xsl:element>	
			</xsl:when>			
			
			<xsl:when test="starts-with(@ID,'__GROUP_MEMORY__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING MEMORY <xsl:value-of select="@ID"/></xsl:message></xsl:if>
  				<xsl:variable name="m_id_" select="substring-after(@ID,'__GROUP_MEMORY__')"/>
			 	<xsl:element name="SET">
			        <xsl:attribute name="ID"><xsl:value-of select="$m_id_"/></xsl:attribute>
			        <xsl:attribute name="CLASS">GROUP</xsl:attribute>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">NAME</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
			        	<xsl:attribute name="VALUE">(Memory) <xsl:value-of select="$m_id_"/></xsl:attribute>
			 		</xsl:element>
			 	   	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
		 		</xsl:element>	
			</xsl:when>	
			
			<xsl:when test="starts-with(@ID,'__GROUP_PERIPHERAL__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING PERIPHERAL <xsl:value-of select="@ID"/></xsl:message></xsl:if>
			 	   	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="starts-with(@ID,'__GROUP_SLAVES__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING SLAVES <xsl:value-of select="@ID"/></xsl:message></xsl:if>
			 	   	<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
			</xsl:when>
<!-- 
			<xsl:when test="starts-with(@ID,'__GROUP_SLAVES__')">
				<xsl:if test="$G_DEBUG='TRUE'"><xsl:message>PLACING SLAVES GOUP <xsl:value-of select="@ID"/></xsl:message></xsl:if>
  				<xsl:variable name="m_id_" select="substring-after(@ID,'__GROUP_SLAVES__')"/>
			 	<xsl:element name="SET">
			        <xsl:attribute name="ID"><xsl:value-of select="$m_id_"/></xsl:attribute>
			        <xsl:attribute name="CLASS">GROUP</xsl:attribute>
			 		<xsl:element name="VARIABLE">
			        	<xsl:attribute name="VIEWDISP">NAME</xsl:attribute>
			        	<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			        	<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
			        	<xsl:attribute name="VALUE">(Slaves of) <xsl:value-of select="$m_id_"/></xsl:attribute>
			 		</xsl:element>
			 	   	<xsl:call-template name="F_Write_XTeller_MODULES">
    					<xsl:with-param name="iModules" select="self::node()"/>
    				</xsl:call-template>	
		 		</xsl:element>	
			</xsl:when>			
-->			
			
		</xsl:choose>
	</xsl:for-each>
</xsl:template>	

	

</xsl:stylesheet>
   
