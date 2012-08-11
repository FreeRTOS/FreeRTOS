<?xml version="1.0" standalone="no"?>

<!DOCTYPE stylesheet [
	<!ENTITY UPPERCASE "ABCDEFGHIJKLMNOPQRSTUVWXYZ">
	<!ENTITY LOWERCASE "abcdefghijklmnopqrstuvwxyz">
	
	<!ENTITY UPPER2LOWER " '&UPPERCASE;' , '&LOWERCASE;' ">
	<!ENTITY LOWER2UPPER " '&LOWERCASE;' , '&UPPERCASE;' ">
	
	<!ENTITY ALPHALOWER "ABCDEFxX0123456789">
	<!ENTITY HEXUPPER "ABCDEFxX0123456789">
	<!ENTITY HEXLOWER "abcdefxX0123456789">
	<!ENTITY HEXU2L " '&HEXLOWER;' , '&HEXUPPER;' ">
]>	        

<xsl:stylesheet version="1.0"
	   xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
       xmlns:exsl="http://exslt.org/common"
       xmlns:dyn="http://exslt.org/dynamic"
       xmlns:math="http://exslt.org/math"
       xmlns:xlink="http://www.w3.org/1999/xlink"
       extension-element-prefixes="math dyn exsl xlink">
           
<!--	
	================================================================================
							Generate XTeller for PORTS
	================================================================================ 
-->	
<xsl:param name="SHOW_IOIF"    select="'TRUE'"/>
<xsl:param name="SHOW_BUSIF"   select="'TRUE'"/>

<xsl:template name="WRITE_VIEW_PORT_TREE">

    <xsl:variable name="num_of_ext_ports_" select="count($G_SYS_EXPS/PORT)"/>
    
	<xsl:if test="$G_DEBUG='TRUE'">
		<xsl:message>WRITING PORT in MODE :<xsl:value-of select="@MODE"/></xsl:message>
		<!-- 
			<xsl:message>EXTERNAL PORT <xsl:value-of select="$num_of_ext_ports_"/></xsl:message>
		 -->
	</xsl:if>	
	
    
	<xsl:if test="$num_of_ext_ports_ &gt; 0">
		<xsl:call-template name="WRITE_VIEW_EXTP_TREE_SET"/>
	</xsl:if>

	<xsl:for-each select="$G_SYS_MODS/MODULE">
		<xsl:sort data-type="number"    select="@ROW_INDEX" order="ascending"/>
		<xsl:variable name= "instName_" select="@INSTANCE"/>
		<xsl:variable name="moduleRef_" select="self::node()"/>
	
		<xsl:call-template name="WRITE_VIEW_PORT_TREE_SET">
			<xsl:with-param name="iModRef" select="$moduleRef_"/>
		</xsl:call-template>
		
	</xsl:for-each>	<!--  End of MODULES loop -->
</xsl:template>

<xsl:template name="WRITE_VIEW_EXTP_TREE_SET">
	
	<xsl:element name="SET">
		<xsl:attribute name="ID">ExternalPorts</xsl:attribute>
		<xsl:attribute name="CLASS">MODULE</xsl:attribute>
		
		<xsl:for-each select="$G_SYS_EXPS">
			
            <xsl:element name="VARIABLE">
				<xsl:attribute name="NAME">Name</xsl:attribute>
				<xsl:attribute name="VALUE">External Ports</xsl:attribute>
				<xsl:attribute name="VIEWDISP">Name</xsl:attribute>
				<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			</xsl:element>				
			
			<xsl:for-each select="PORT">
				<xsl:sort select="@NAME" order="ascending"/>
				<!--
				<xsl:sort data-type="number" select="@MHS_INDEX" order="ascending"/>
				  -->
			
				<xsl:element name="SET">
					<xsl:attribute name="ID"><xsl:value-of select="@NAME"/></xsl:attribute>
					<xsl:attribute name="CLASS">PORT</xsl:attribute>
					<xsl:attribute name="ROW_INDEX"><xsl:value-of select="(position() - 1)"/></xsl:attribute>
			
					<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"       NAME="SIGNAME" VALUE="{@SIGNAME}" IS_EDITABLE="TRUE"/>
					<VARIABLE VIEWTYPE="TEXTBOX"   VIEWDISP="Name"      NAME="NAME"    VALUE="{@NAME}"/>
					<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Direction" NAME="DIR"     VALUE="{@DIR}"/>
				            
					<xsl:if test="(@SIGIS)">
						<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Class"     NAME="SIGIS"   VALUE="{@SIGIS}"/>
					</xsl:if>
					<xsl:if test="not(@SIGIS)">
						<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Class"     NAME="SIGIS"   VALUE="NONE"/>
					</xsl:if>
				            
				    <xsl:choose>
						<xsl:when test="@LEFT and @RIGHT">
							<xsl:variable name="vecformula_txt_">[<xsl:value-of select="@LEFT"/>:<xsl:value-of select="@RIGHT"/>]</xsl:variable>
							<VARIABLE VIEWTYPE="TEXTBOX"    VIEWDISP="Range" NAME="VECFORMULA" VALUE="{$vecformula_txt_}"/>
						</xsl:when>
						<xsl:when test="@MSB and @LSB">
							<xsl:variable name="vecformula_txt_">[<xsl:value-of select="@MSB"/>:<xsl:value-of select="@LSB"/>]</xsl:variable>
							<VARIABLE VIEWTYPE="TEXTBOX"    VIEWDISP="Range" NAME="VECFORMULA" VALUE="{$vecformula_txt_}"/>
						</xsl:when>
				    	<xsl:when test="(not(@MSB) and not(@LSB) and not(@SIGIS = 'CLK') and not(@SIGIS = 'CLOCK') and not(@SIGIS = 'DCMCLK') and not(@SIGIS = 'RST') and not(@SIGIS = 'RESET'))">
				    		<VARIABLE VIEWTYPE="TEXTBOX"    VIEWDISP="Range" NAME="VECFORMULA" VALUE=""/>
				    	</xsl:when>
				    </xsl:choose>        
				                 
				    <xsl:if test="((@SIGIS = 'CLK') or (@SIGIS = 'CLOCK') or (@SIGIS = 'DCMCLK'))">
				    	<VARIABLE VIEWTYPE="TEXTBOX"  VIEWDISP="Frequency(Hz)" NAME="CLKFREQUENCY" VALUE="{@CLKFREQUENCY}"/>
				    </xsl:if>
				    
				   	<xsl:if test="(@SIGIS = 'RST' or @SIGIS = 'RESET')">
				   		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Reset Polarity" NAME="RSTPOLARITY" VALUE="{@RSTPOLARITY}"/>
					</xsl:if>
					
		            <xsl:if test="(@SIGIS = 'INTERRUPT')">
	            		<VARIABLE VIEWTYPE="DROPDOWN"    VIEWDISP="Sensitivity" NAME="SENSITIVITY" VALUE="{@SENSITIVITY}"/>
	        		</xsl:if>
	        	</xsl:element>
			</xsl:for-each> <!--  End of EXTERNAL PORTS loop -->
		</xsl:for-each> <!-- End of EXTERNAL PORTS loop  -->
	</xsl:element>	<!-- End of EXTERNAL PORTS SET  -->
</xsl:template>

<xsl:template name="WRITE_VIEW_PORT_TREE_SET">
	<xsl:param name="iModRef" select="'__NONE__'"/>
	
	<xsl:variable name="m_inst_"      select="$iModRef/@INSTANCE"/>
	<xsl:variable name="m_class_"     select="$iModRef/@MODCLASS"/>
	<xsl:variable name="m_type_"      select="$iModRef/@MODTYPE"/>
	<xsl:variable name="m_type_lc_"   select="translate($m_type_,&UPPER2LOWER;)"/> 
	<xsl:variable name="m_version_"   select="$iModRef/@HWVERSION"/>
	<xsl:variable name="m_licinfo_"   select="$iModRef/LICENSEINFO"/>	
	<xsl:variable name="m_ports_"     select="$iModRef/PORTS"/>	
	
	<xsl:variable name="is_axi_interconnect_">
        <xsl:choose>
            <xsl:when test="$m_type_    = 'axi_interconnect'">TRUE</xsl:when>
            <xsl:when test="$m_type_lc_ = 'axi_interconnect'">TRUE</xsl:when>
            <xsl:otherwise>FALSE</xsl:otherwise>
        </xsl:choose>
	</xsl:variable>		

	<xsl:for-each select="$G_SYS_MODS"> <!--  To put things in the right scope for the keys below -->
	
		<xsl:variable name="m_iofs_all_"  select="key('G_MAP_ALL_IOFS', $m_inst_)"/>	
		<xsl:variable name="m_bifs_all_"  select="key('G_MAP_ALL_BIFS', $m_inst_)"/>	
		
		<xsl:variable name="m_ports_def_" select="key('G_MAP_DEF_PORTS',$m_inst_)"/>	
		<xsl:variable name="m_ports_ndf_" select="key('G_MAP_NDF_PORTS',$m_inst_)"/>	
<!-- 
		<xsl:if test="$G_DEBUG = 'TRUE'">
			<xsl:message><xsl:value-of select="$m_inst_"/> has <xsl:value-of select="count($m_bifs_all_)"/> valid bifs </xsl:message>         
			<xsl:message><xsl:value-of select="$m_inst_"/> has <xsl:value-of select="count($m_iofs_all_)"/> valid iofs </xsl:message>         
			<xsl:message><xsl:value-of select="$m_inst_"/> has <xsl:value-of select="count($m_ports_def_)"/> default ports </xsl:message>         
			<xsl:message><xsl:value-of select="$m_inst_"/> has <xsl:value-of select="count($m_ports_ndf_)"/> non default ports </xsl:message>         
			<xsl:message></xsl:message>
		</xsl:if>
-->		
	
		<SET ID="{$m_inst_}" CLASS="MODULE">
			<!-- CR452579
		     			Can only modify INSTANCE name in Hierarchal view.
			--> 
			<VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Name"       NAME="INSTANCE"  VALUE="{$m_inst_}"/>
			<VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$m_type_}" VIEWICON="{$m_licinfo_/@ICON_NAME}"/>
			<VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$m_version_}"/>
			
			<!-- 
			CR582477, 
				(among others) special case of axi_interconnect_aclk which is a member of
				a bus interface, but should be treated as a non interface port, (i.e. appear even
				if the bus interfaces its a member of is invalid.
			-->
		 	<xsl:if test="($is_axi_interconnect_ = 'TRUE')">
		 		<!--  do it this way so we also catch the lower-upper case mismatches -->
				<xsl:for-each select="key('G_MAP_ALL_PORTS',$m_inst_)[contains(@SIGIS,'CLK')]">
					<xsl:variable name="uc_portName_" select="translate(@NAME,&LOWER2UPPER;)"/> 
		 	    	<xsl:if test="($uc_portName_= 'INTERCONNECT_ACLK')">
		 	    		<!-- 
							<xsl:message><xsl:value-of select="$m_inst_"/>.<xsl:value-of select="@NAME"/> =  <xsl:value-of select="@SIGIS"/></xsl:message>
		 	    		 -->
						<xsl:variable name="portName_" select="@NAME"/> 
						<xsl:variable name="portDir_"  select="@DIR"/> 
						<xsl:variable name="portSig_"  select="@SIGNAME"/> 
				
						<xsl:variable name="portSigIs_">
							<xsl:choose>
								<xsl:when test="not(@SIGIS)">__NONE__</xsl:when>
				    			<xsl:otherwise><xsl:value-of select="@SIGIS"/></xsl:otherwise>
							</xsl:choose>	
						</xsl:variable>
				
						<xsl:variable name="portSensi_">
							<xsl:choose>
								<xsl:when test="(@SENSITIVITY)"><xsl:value-of select="@SENSITIVIITY"/></xsl:when>
				  	  			<xsl:otherwise>__NONE__</xsl:otherwise>
							</xsl:choose>
						</xsl:variable>
							
						<xsl:variable name="portVecFormula_">
				    		<xsl:choose>
								<xsl:when test="@VECFORMULA"><xsl:value-of select="@VECFORMULA"/></xsl:when>
				    			<xsl:otherwise>__NONE__</xsl:otherwise>
							</xsl:choose>
						</xsl:variable>    
				
						<xsl:call-template name="WRITE_PORT_SET">
							<xsl:with-param name="iName"        select="$portName_"/>
							<xsl:with-param name="iDir"  	    select="$portDir_"/>
							<xsl:with-param name="iSigName"     select="$portSig_"/>
							<xsl:with-param name="iSigIs"       select="$portSigIs_"/>
							<xsl:with-param name="iSensitivity" select="$portSensi_"/>
							<xsl:with-param name="iVecFormula"  select="$portVecFormula_"/>
						</xsl:call-template>
			    	</xsl:if>
				</xsl:for-each>
		 	</xsl:if>
			
			<!--  PORTS not part of an INTERFACE -->
		 	<xsl:for-each select="$m_ports_ndf_">
		 	
				<xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
				<xsl:variable name="uc_portName_" select="translate(@NAME,&LOWER2UPPER;)"/> 
				
				<!-- 
		 	    <xsl:if test="((not(@BUS) and not(@IOS)) or (($is_axi_interconnect_ = 'TRUE') and ($uc_portName_= 'INTERCONNECT_ACLK')))">
			    </xsl:if>
				 -->
			    
		 	    
				<xsl:variable name="portName_" select="@NAME"/> 
				<xsl:variable name="portDir_"  select="@DIR"/> 
				<xsl:variable name="portSig_"  select="@SIGNAME"/> 
		
				<xsl:variable name="portSigIs_">
					<xsl:choose>
						<xsl:when test="not(@SIGIS)">__NONE__</xsl:when>
		    			<xsl:otherwise><xsl:value-of select="@SIGIS"/></xsl:otherwise>
					</xsl:choose>	
				</xsl:variable>
		
				<xsl:variable name="portSensi_">
					<xsl:choose>
						<xsl:when test="(@SENSITIVITY)"><xsl:value-of select="@SENSITIVIITY"/></xsl:when>
		  	  			<xsl:otherwise>__NONE__</xsl:otherwise>
					</xsl:choose>
				</xsl:variable>
					
				<xsl:variable name="portVecFormula_">
		    		<xsl:choose>
						<xsl:when test="@VECFORMULA"><xsl:value-of select="@VECFORMULA"/></xsl:when>
		    			<xsl:otherwise>__NONE__</xsl:otherwise>
					</xsl:choose>
				</xsl:variable>    
		
		     
				<xsl:call-template name="WRITE_PORT_SET">
					<xsl:with-param name="iName"        select="$portName_"/>
					<xsl:with-param name="iDir"  	    select="$portDir_"/>
					<xsl:with-param name="iSigName"     select="$portSig_"/>
					<xsl:with-param name="iSigIs"       select="$portSigIs_"/>
					<xsl:with-param name="iSensitivity" select="$portSensi_"/>
					<xsl:with-param name="iVecFormula"  select="$portVecFormula_"/>
				</xsl:call-template>
		   	</xsl:for-each>	<!--  END of PORTS NOT OF INTERFACE -->
		   	
			<!--  PORTS part of a BUSINTERFACE -->
			<xsl:if test="$SHOW_BUSIF = 'TRUE'">
				<xsl:for-each select="$m_bifs_all_">
				    <xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
				    
					<xsl:variable name="bifName_"      select="@NAME"/>
			        <xsl:variable name="bifRef_"       select="self::node()"/>
			        <xsl:variable name="portmapsRef_"  select="$bifRef_/PORTMAPS"/>
					
					<!-- 
			        	<xsl:variable name="bpmsCnt_"  select="count($bpmsRef_/PORTMAP)"/>
					 	<xsl:message><xsl:value-of select="$instName_"/>.<xsl:value-of select="$bifName_"/>.<xsl:value-of select="$bpmsCnt_"/></xsl:message>
					 -->
					 
		   			<xsl:variable name="is_external_">
		  				<xsl:call-template name="F_IS_Interface_External">
		  			   		<xsl:with-param name="iInstRef" select="$iModRef"/>
		  			   		<xsl:with-param name="iIntfRef" select="$bifRef_"/>
		  			   	</xsl:call-template>	
				   	</xsl:variable>
		 			   		
		    		<xsl:variable name="bif_connection_">
			    		<xsl:choose>
							<xsl:when test="not(@BUSNAME = '__NOC__')">Connected to BUS <xsl:value-of select="@BUSNAME"/></xsl:when>
							<xsl:when test="($is_external_ = 'TRUE')">Connected to External Ports</xsl:when>
			    			<xsl:otherwise>Not connected to BUS or External Ports</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
										
		           <!--  <SET ID="{@NAME}" CLASS="BUSINTERFACE.PORTS"/> --> 
			        <xsl:element name="SET">
		            
		                <xsl:attribute name="ID"><xsl:value-of select="@NAME"/></xsl:attribute>
		                <xsl:attribute name="CLASS">BUSINTERFACE.PORTS</xsl:attribute>
		                
		                <xsl:if test="$is_external_ = 'TRUE'">
		                	<xsl:attribute name="IS_EXTERNAL">TRUE</xsl:attribute>
		                </xsl:if>
		                
		            	<VARIABLE VIEWTYPE="STATIC"   VIEWDISP="NAME" NAME="NAME" VALUE="(BUS_IF) {@NAME}"/>
		              	<VARIABLE VIEWTYPE="DROPDOWN" VIEWDISP="Net"  NAME="BUSINTERFACE.CONNECTION" VALUE="{$bif_connection_}"/>
		              		
						<xsl:for-each select="$portmapsRef_/PORTMAP">
			        		
						    <xsl:variable name="portDir_"  select="@DIR"/> 
					    	<xsl:variable name="portName_" select="@PHYSICAL"/> 
			        		
					    	<xsl:if test="$m_ports_def_[(@NAME = $portName_)]"><!--  Only in map if port is valid -->
					    	
							    <!-- 
					    	       <xsl:if test="(not($portRef_/@IS_VALID) or ($portRef_/@IS_VALID = 'TRUE'))"/>
						    		<xsl:sort select="@MPD_INDEX" order="ascending"/>
							    	<xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
							     -->
			        		    <xsl:variable name="portRef_"  select="$m_ports_def_[(@NAME = $portName_)]"/>
						    	<xsl:variable name="portSig_"  select="$portRef_/@SIGNAME"/>
				
						    	<xsl:variable name="portSigIs_">
							    	<xsl:choose>
										<xsl:when test="not($portRef_/@SIGIS)">__NONE__</xsl:when>
							    		<xsl:otherwise><xsl:value-of select="$portRef_/@SIGIS"/></xsl:otherwise>
									</xsl:choose>	
								</xsl:variable>
							
					    		<xsl:variable name="portSensi_">
								    <xsl:choose>
										<xsl:when test="($portRef_/@SENSITIVITY)"><xsl:value-of select="$portRef_/@SENSITIVITY"/></xsl:when>
								    	<xsl:otherwise>__NONE__</xsl:otherwise>
									</xsl:choose>
								</xsl:variable>
											
							    <xsl:variable name="portVecFormula_">
								    <xsl:choose>
										<xsl:when test="$portRef_/@VECFORMULA"><xsl:value-of select="$portRef_/@VECFORMULA"/></xsl:when>
								    	<xsl:otherwise>__NONE__</xsl:otherwise>
									</xsl:choose>
								</xsl:variable>
							    
				   			   	<xsl:call-template name="WRITE_PORT_SET">
									<xsl:with-param name="iName"        select="$portName_"/>
									<xsl:with-param name="iDir"  	    select="$portDir_"/>
									<xsl:with-param name="iSigName"     select="$portSig_"/>
									<xsl:with-param name="iSigIs"       select="$portSigIs_"/>
									<xsl:with-param name="iSensitivity" select="$portSensi_"/>
									<xsl:with-param name="iVecFormula"  select="$portVecFormula_"/>
							  	</xsl:call-template>
					    	</xsl:if>
						</xsl:for-each> <!--  END BIF PORTMAPS LOOP -->	               		
		             	</xsl:element>
				</xsl:for-each> <!-- END BIFS LOOP -->
			</xsl:if> <!--  END IF SHOW_BUSIFS --> 
			
			
			<!--  PORTS part of a IOINTERFACE -->
			<xsl:if test="$SHOW_IOIF = 'TRUE'">
			
				<xsl:for-each select="$m_iofs_all_[PORTMAPS/PORTMAP]">
				    <xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
				    
					<xsl:variable name="iifName_" select="@NAME"/>
			        <xsl:variable name="iifRef_"  select="self::node()"/>
			        <xsl:variable name="portmapsRef_" select="$iifRef_/PORTMAPS"/>
					
					<xsl:variable name="is_external_">
		   			   	<xsl:call-template name="F_IS_Interface_External">
		   			   		<xsl:with-param name="iInstRef" select="$iModRef"/>
		   			   		<xsl:with-param name="iIntfRef" select="$iifRef_"/>
		   			   	</xsl:call-template>	
		  			   	</xsl:variable>
		  			   	
			   		<xsl:variable name="iif_connection_">
				   		<xsl:choose>
							<xsl:when test="($is_external_ ='TRUE')">Connected to External Ports</xsl:when>
							<xsl:otherwise>Not connected to External Ports</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
					
		        	<xsl:element name="SET">
		           
		               	<xsl:attribute name="ID"><xsl:value-of select="@NAME"/></xsl:attribute>
		               	<xsl:attribute name="CLASS">IOINTERFACE.PORTS</xsl:attribute>
		               
		               	<xsl:if test="$is_external_ = 'TRUE'">
		               		<xsl:attribute name="IS_EXTERNAL">TRUE</xsl:attribute>
		               	</xsl:if>
		               
			            <VARIABLE VIEWTYPE="STATIC"    VIEWDISP="NAME" NAME="NAME" VALUE="(IO_IF) {@NAME}"/>
		                <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="IOINTERFACE.CONNECTION" VALUE="{$iif_connection_}"/>
						
						<xsl:for-each select="$portmapsRef_/PORTMAP">
			        		
					    	<xsl:variable name="portName_" select="@PHYSICAL"/>
					    	<xsl:variable name="portDir_"  select="@DIR"/>
			        		
					        <!--
					        <xsl:variable name="port_is_valid_">
					        	<xsl:choose>
					        		<xsl:when test="$portRef_/@IS_VALID = 'FALSE'">FALSE</xsl:when>
					        		<xsl:otherwise>TRUE</xsl:otherwise>
					        	</xsl:choose>
					        </xsl:variable>						    	
						   <xsl:message><xsl:value-of select="$portName_"/> : <xsl:value-of select="$port_is_valid_"/> : <xsl:value-of select="$portRef_/@IS_VALID"/></xsl:message>    
					         -->
						   
					        <xsl:if test="$m_ports_def_[(@NAME = $portName_)]"> <!--  Only in map if port is valid -->
					           <!-- 
						  	   <xsl:message><xsl:value-of select="$portName_"/> </xsl:message>
					            -->
					        
			        			<xsl:variable name="portRef_"  select="$m_ports_def_[(@NAME = $portName_)]"/>
					    		<xsl:variable name="portSig_"  select="$portRef_/@SIGNAME"/>
				
						    	<xsl:variable name="portSigIs_">
							    	<xsl:choose>
										<xsl:when test="not($portRef_/@SIGIS)">__NONE__</xsl:when>
							    		<xsl:otherwise><xsl:value-of select="$portRef_/@SIGIS"/></xsl:otherwise>
									</xsl:choose>	
								</xsl:variable>
							
					    		<xsl:variable name="portSensi_">
								    <xsl:choose>
										<xsl:when test="($portRef_/@SENSITIVITY)"><xsl:value-of select="$portRef_/@SENSITIVITY"/></xsl:when>
								    	<xsl:otherwise>__NONE__</xsl:otherwise>
									</xsl:choose>
								</xsl:variable>
											
							    <xsl:variable name="portVecFormula_">
								    <xsl:choose>
										<xsl:when test="$portRef_/@VECFORMULA"><xsl:value-of select="$portRef_/@VECFORMULA"/></xsl:when>
								    	<xsl:otherwise>__NONE__</xsl:otherwise>
									</xsl:choose>
								</xsl:variable>
							    
				   			   	<xsl:call-template name="WRITE_PORT_SET">
									<xsl:with-param name="iName"        select="$portName_"/>
									<xsl:with-param name="iDir"  	    select="$portDir_"/>
									<xsl:with-param name="iSigName"     select="$portSig_"/>
									<xsl:with-param name="iSigIs"       select="$portSigIs_"/>
									<xsl:with-param name="iSensitivity" select="$portSensi_"/>
									<xsl:with-param name="iVecFormula"  select="$portVecFormula_"/>
							  	</xsl:call-template>
					        </xsl:if> <!-- End of port is valid check -->
						</xsl:for-each> <!--  END IO INTERFACE PORTMAPS LOOP -->	 
					</xsl:element>
				</xsl:for-each> <!-- END IIFS LOOP -->
			</xsl:if> <!--  END IF SHOW_IOIFS -->				
		</SET>	
	
	</xsl:for-each> <!-- End of the scoping for key functions-->
</xsl:template>

<xsl:template name="WRITE_VIEW_PORT_FLAT">
	
	<xsl:if test="$G_DEBUG='TRUE'">
		<xsl:message>WRITING PORT MODE <xsl:value-of select="@MODE"/></xsl:message>
	</xsl:if>	
	
    <xsl:variable name="num_of_ext_ports_" select="count($G_SYS_EXPS/PORT)"/>
	<xsl:if test="$num_of_ext_ports_ &gt; 0">
		<xsl:call-template name="WRITE_VIEW_EXTP_FLAT_SET"/>
	</xsl:if>
	
	
    <xsl:for-each select="$G_SYS_MODS/MODULE">
  		<xsl:sort data-type="number" select="@ROW_INDEX" order="ascending"/>
		<xsl:variable name="instName_" select="@INSTANCE"/>
		<xsl:variable name="moduleRef_" select="self::node()"/>
	
		<xsl:call-template name="WRITE_VIEW_PORT_FLAT_SET">
			<xsl:with-param name="iModRef" select="$moduleRef_"/>
		</xsl:call-template>
	   		
    </xsl:for-each> <!-- End of Modules Loop -->
</xsl:template>	

<xsl:template name="WRITE_VIEW_EXTP_FLAT_SET">

	<xsl:for-each select="$G_SYS_EXPS">
  		<xsl:for-each select="PORT[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
			<xsl:sort data-type="number" select="@MHS_INDEX" order="ascending"/> 
		    <xsl:variable name="ext_is_interrupt_">
			   <xsl:if test="@SIGIS = 'INTERRUPT'">TRUE</xsl:if>
			   <xsl:if test="not(@SIGIS = 'INTERRUPT')">FALSE</xsl:if>
		    </xsl:variable>
			  
 			<SET ID="{@NAME}" CLASS="PORT">
			 
				<VARIABLE VIEWTYPE="STATIC"  VIEWDISP="Instance" NAME="INSTANCE" VALUE="External Ports"/>
      			<VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Port Name" NAME="NAME" VALUE="{@NAME}"/>
      			
				 <xsl:choose>
					<xsl:when test="@LEFT and @RIGHT">
						<xsl:variable name="vecformula_txt_">[<xsl:value-of select="@LEFT"/>:<xsl:value-of select="@RIGHT"/>]</xsl:variable>
						<VARIABLE VIEWTYPE="TEXTBOX"    VIEWDISP="Range" NAME="VECFORMULA" VALUE="{$vecformula_txt_}"/>
					</xsl:when>
					<xsl:when test="@MSB and @LSB">
						<xsl:variable name="vecformula_txt_">[<xsl:value-of select="@MSB"/>:<xsl:value-of select="@LSB"/>]</xsl:variable>
						<VARIABLE VIEWTYPE="TEXTBOX"    VIEWDISP="Range" NAME="VECFORMULA" VALUE="{$vecformula_txt_}"/>
					</xsl:when>
			    	<xsl:when test="(not(@MSB) and not(@LSB) and not(@SIGIS = 'CLK') and not(@SIGIS = 'CLOCK') and not(@SIGIS = 'DCMCLK') and not(@SIGIS = 'RST') and not(@SIGIS = 'RESET'))">
			    		<VARIABLE VIEWTYPE="TEXTBOX"    VIEWDISP="Range" NAME="VECFORMULA" VALUE=""/>
			    	</xsl:when>
			    </xsl:choose>
			    
	       		<VARIABLE VIEWTYPE="DROPDOWN" VIEWDISP="Net" NAME="SIGNAME" VALUE="{@SIGNAME}" IS_EDITABLE="TRUE"/>
	       		<VARIABLE VIEWTYPE="DROPDOWN" VIEWDISP="Direction" NAME="DIR" VALUE="{@DIR}"/>
	       		
   				<xsl:if test="(@SIGIS)">
					<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Class"     NAME="SIGIS"   VALUE="{@SIGIS}"/>
		        </xsl:if>
				<xsl:if test="not(@SIGIS)">
					<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Class"     NAME="SIGIS"   VALUE="NONE"/>
				</xsl:if>
				
				<xsl:if test="(@SIGIS = 'RST' or @SIGIS = 'RESET')">
	       			<VARIABLE VIEWTYPE="DROPDOWN" VIEWDISP="Reset Polarity" NAME="RSTPOLARITY" VALUE="{@RSTPOLARITY}"/>
				</xsl:if>
				<xsl:if test="((@SIGIS = 'CLK') or (@SIGIS = 'CLOCK') or (@SIGIS = 'DCMCLK'))">
	       			<VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Frequency(Hz)" NAME="CLKFREQUENCY" VALUE="{@CLKFREQUENCY}"/>
				</xsl:if>
				
				<!-- SENSITIVITY Settings on Interrupt ports -->
				<xsl:choose>
					<xsl:when test="((@SIGNAME = '__NOC__') and ($ext_is_interrupt_ = 'TRUE') and not(@SENSITIVITY))">
		        		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Sensitivity"  NAME="SENSITIVITY" VALUE=""/> 
					</xsl:when>
					<xsl:when test="((@SIGNAME = '__NOC__') and ($ext_is_interrupt_ = 'TRUE') and (@SENSITIVITY))">
		        		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Sensitivity"  NAME="SENSITIVITY" VALUE="{@SENSITIVITY}"/>
					</xsl:when>
					
					<xsl:when test="((@SIGNAME = '__DEF__') and ($ext_is_interrupt_ = 'TRUE') and not(@SENSITIVITY))">
		        		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Sensitivity"  NAME="SENSITIVITY" VALUE=""/>
					</xsl:when>
					<xsl:when test="((@SIGNAME = '__DEF__') and ($ext_is_interrupt_ = 'TRUE') and (@SENSITIVITY))">
		        		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Sensitivity"  NAME="SENSITIVITY" VALUE="{@SENSITIVITY}"/>
					</xsl:when>
					
					<xsl:when test="(not(@SIGNAME = '__DEF__') and not(@SIGNAME = '__NOC__') and ($ext_is_interrupt_ = 'TRUE') and not(@SENSITIVITY))">
		        		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Sensitivity"  NAME="SENSITIVITY" VALUE=""/> 
					</xsl:when>
					
					<xsl:when test="(not(@SIGNAME = '__DEF__') and not(@SIGNAME = '__NOC__') and ($ext_is_interrupt_ = 'TRUE') and (@SENSITIVITY))">
		        		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Sensitivity"  NAME="SENSITIVITY" VALUE="{@SENSITIVITY}"/> 
					</xsl:when>
				</xsl:choose>
			</SET>				
   	    </xsl:for-each>
	</xsl:for-each>
</xsl:template>

<xsl:template name="WRITE_VIEW_PORT_FLAT_SET">

	<xsl:param name="iModRef" 		  select="'__NONE__'"/>
	
	<xsl:variable name="m_inst_"      select="$iModRef/@INSTANCE"/>
	<xsl:variable name="m_class_"     select="$iModRef/@MODCLASS"/>
	<xsl:variable name="m_type_"      select="$iModRef/@MODTYPE"/>
	<xsl:variable name="m_type_lc_"   select="translate($m_type_,&UPPER2LOWER;)"/> 
	<xsl:variable name="m_version_"   select="$iModRef/@HWVERSION"/>
	<xsl:variable name="m_licinfo_"   select="$iModRef/LICENSEINFO"/>	
	
	<xsl:variable name="is_axi_interconnect_">
        <xsl:choose>
            <xsl:when test="$m_type_    = 'axi_interconnect'">TRUE</xsl:when>
            <xsl:when test="$m_type_lc_ = 'axi_interconnect'">TRUE</xsl:when>
            <xsl:otherwise>FALSE</xsl:otherwise>
        </xsl:choose>
	</xsl:variable>
	
	<xsl:for-each select="$G_SYS_MODS"> <!--  To put things in the right scope for the keys below -->
	
		<xsl:variable name="m_bifs_all_"  select="key('G_MAP_ALL_BIFS', $m_inst_)"/>
		<xsl:variable name="m_ports_all_" select="key('G_MAP_ALL_PORTS',$m_inst_)"/>	
		
		<xsl:if test="$G_DEBUG = 'TRUE'">
			<xsl:message><xsl:value-of select="$m_inst_"/> has <xsl:value-of select="count($m_ports_all_)"/> valid ports </xsl:message>         
		</xsl:if>
		
		<xsl:for-each select="$m_ports_all_">
			<xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
	        <!-- <xsl:message>PORTNM : <xsl:value-of select="@NAME"/></xsl:message> -->
	        
			<xsl:variable name="p_nm_uc_"  select="translate(@NAME,&LOWER2UPPER;)"/> 
			<xsl:variable name="p_bif_"    select="@BUS"/>	        
			
	        <xsl:variable name="port_is_valid_">
	        	<xsl:choose>
	        		<xsl:when test="@IS_VALID = 'FALSE'">FALSE</xsl:when>
	        		<xsl:when test="(($is_axi_interconnect_ = 'TRUE') and ($p_nm_uc_= 'INTERCONNECT_ACLK'))">TRUE</xsl:when>
	        		<xsl:when test="not(@BUS) or (@BUS and key('G_MAP_ALL_BIFS', $m_inst_)[(@NAME = $p_bif_)])">TRUE</xsl:when>
	        		<xsl:otherwise>FALSE</xsl:otherwise>
	        	</xsl:choose>
	        </xsl:variable>
	        
		    <xsl:if test="$port_is_valid_ = 'TRUE'">
		    <!-- 
    		  	<xsl:message>PORT <xsl:value-of select="@BUS"/>.<xsl:value-of select="@NAME"/></xsl:message> 
		     -->
				<SET ID="{@NAME}" CLASS="PORT">
				<!--        
				CR452579
				Can only modify INSTANCE name in Hierarchal view.
				--> 
				    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$m_inst_}"/>
				    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$m_type_}" VIEWICON="{$m_licinfo_/@ICON_NAME}"/>
				    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$m_version_}"/>
				       
				    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Port Name"  NAME="NAME" VALUE="{@NAME}"/>
				    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Direction"  NAME="DIR"  VALUE="{@DIR}"/>
				    
				    <xsl:if test="@SIGIS">
				        <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="Class" NAME="SIGIS" VALUE="{@SIGIS}"/>
				    </xsl:if>
				    
				    <xsl:if test="@VECFORMULA">
				        <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="Range" NAME="VECFORMULA" VALUE="{@VECFORMULA}"/>
				    </xsl:if>
				    
				    <xsl:if test="@SENSITIVITY">
				        <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="Sensitivity" NAME="SENSITIVITY" VALUE="{@SENSITIVITY}"/>
				    </xsl:if>
				    
				    <xsl:variable name="is_interrupt">
				       <xsl:if test="@SIGIS = 'INTERRUPT'">TRUE</xsl:if>
				       <xsl:if test="not(@SIGIS = 'INTERRUPT')">FALSE</xsl:if>
				    </xsl:variable>
				    
				   <xsl:variable name="is_input">
					    <xsl:choose> 
					        <xsl:when test="(@DIR= 'I')">TRUE</xsl:when>
					        <xsl:when test="(@DIR= 'IN')">TRUE</xsl:when>
					        <xsl:when test="(@DIR= 'INPUT')">TRUE</xsl:when>
					        <xsl:otherwise>FALSE</xsl:otherwise>
					    </xsl:choose>
				    </xsl:variable>
				    
				    <!-- VECFORMULA Settings if Interrupt settings -->
				    <xsl:choose>
				        
				        <xsl:when test="((@SIGNAME = '__NOC__') and ($is_interrupt = 'TRUE') and ($is_input = 'TRUE') and not(@VECFORMULA))">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="No Connection" IS_INTERRUPT="{$is_interrupt}"/>
				        </xsl:when>
				        
				        <xsl:when test="((@SIGNAME = '__NOC__') and ($is_interrupt = 'TRUE') and ($is_input = 'TRUE') and (@VECFORMULA))">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="No Connection" IS_INTERRUPT="{$is_interrupt}" IS_RANGE="TRUE"/>
				        </xsl:when>
				        
				        <xsl:when test="@SIGNAME = '__NOC__'">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="No Connection" IS_EDITABLE="TRUE"/>
				        </xsl:when>
				        
				        <xsl:when test="((@SIGNAME = '__DEF__') and ($is_interrupt = 'TRUE') and ($is_input = 'TRUE') and not(@VECFORMULA))">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="Default Connection" IS_INTERRUPT="{$is_interrupt}"/>
				        </xsl:when>
				        <xsl:when test="((@SIGNAME = '__DEF__') and ($is_interrupt = 'TRUE') and ($is_input = 'TRUE') and (@VECFORMULA))">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="Default Connection" IS_INTERRUPT="{$is_interrupt}" IS_RANGE="TRUE"/>
				        </xsl:when>
				        <xsl:when test="@SIGNAME = '__DEF__'">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="Default Connection"/>
				        </xsl:when>
				        
				        <xsl:when test="(not(@SIGNAME = '__DEF__') and not(@SIGNAME = '__NOC__') and ($is_input = 'TRUE') and ($is_interrupt = 'TRUE') and (@VECFORMULA))">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="{@SIGNAME}" IS_INTERRUPT="{$is_interrupt}" IS_RANGE="TRUE"/>
				        </xsl:when>
				        <xsl:when test="(not(@SIGNAME = '__DEF__') and not(@SIGNAME = '__NOC__') and ($is_input = 'TRUE') and ($is_interrupt = 'TRUE'))">
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="{@SIGNAME}" IS_INTERRUPT="{$is_interrupt}"/>
				        </xsl:when>
				            
				        <xsl:otherwise>     
				            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="{@SIGNAME}" IS_EDITABLE="TRUE"/>
				        </xsl:otherwise>
				    </xsl:choose>
				  </SET>
			</xsl:if>  <!--  End of port validity check -->
		</xsl:for-each>  <!-- End of Ports Loop -->
	</xsl:for-each>
</xsl:template>

<xsl:template name="WRITE_PORT_SET">

<xsl:param name="iName"	        select="'__NONE__'"/>
<xsl:param name="iDir"          select="'__NONE__'"/>
<xsl:param name="iSigName"      select="'__NONE__'"/>
<xsl:param name="iSigIs"        select="'__NONE__'"/>
<xsl:param name="iVecFormula"   select="'__NONE__'"/>
<xsl:param name="iSensitivity"  select="'__NONE__'"/>

<SET ID="{$iName}" CLASS="PORT">
 
   <VARIABLE VIEWTYPE="STATIC"  VIEWDISP="NAME" NAME="NAME" VALUE="{$iName}"/>
    
   <xsl:variable name="is_interrupt">
       <xsl:if test="$iSigIs = 'INTERRUPT'">TRUE</xsl:if>
       <xsl:if test="not($iSigIs = 'INTERRUPT')">FALSE</xsl:if>
   </xsl:variable>
    
   <xsl:variable name="is_input">
        <xsl:choose> 
            <xsl:when test="($iDir = 'I')">TRUE</xsl:when>
            <xsl:when test="($iDir = 'IN')">TRUE</xsl:when>
            <xsl:when test="($iDir = 'INPUT')">TRUE</xsl:when>
            <xsl:otherwise>FALSE</xsl:otherwise>
        </xsl:choose>
   </xsl:variable>
   
   <xsl:choose>
   
        <xsl:when test="(($iSigName = '__NOC__') and ($is_input = 'TRUE') and ($is_interrupt = 'TRUE') and ($iVecFormula = '__NONE__'))">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="No Connection" IS_INTERRUPT="{$is_interrupt}"/>
        </xsl:when>
        <xsl:when test="(($iSigName = '__NOC__') and ($is_input ='TRUE') and ($is_interrupt = 'TRUE') and not($iVecFormula = '__NONE__'))">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="No Connection" IS_INTERRUPT="{$is_interrupt}" IS_RANGE="TRUE"/>
        </xsl:when>
        <xsl:when test="$iSigName = '__NOC__'">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="No Connection" IS_EDITABLE="TRUE"/>
        </xsl:when>
       
        <xsl:when test="(($iSigName = '__DEF__') and ($is_input = 'TRUE') and ($is_interrupt = 'TRUE') and ($iVecFormula = '__NONE__'))">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="Default Connection" IS_INTERRUPT="{$is_interrupt}"/>
        </xsl:when>
        <xsl:when test="(($iSigName = '__DEF__') and ($is_input = 'TRUE') and ($is_interrupt = 'TRUE') and not($iVecFormula = '__NONE__'))">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="Default Connection" IS_INTERRUPT="{$is_interrupt}" IS_RANGE="TRUE"/>
        </xsl:when>
        
        <xsl:when test="($iSigName = '__DEF__')">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="Default Connection"/>
        </xsl:when>
        
        <xsl:when test="(not($iSigName = '__DEF__') and not($iSigName = '__NOC__') and ($is_input ='TRUE') and ($is_interrupt = 'TRUE') and not($iVecFormula = '__NONE__'))">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="{$iSigName}" IS_INTERRUPT="{$is_interrupt}" IS_RANGE="TRUE"/>
        </xsl:when>
        
        <xsl:when test="(not($iSigName = '__DEF__') and not($iSigName = '__NOC__') and ($is_input ='TRUE') and ($is_interrupt = 'TRUE'))">
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="{$iSigName}" IS_INTERRUPT="{$is_interrupt}"/>
        </xsl:when>
            
        <xsl:otherwise>     
            <VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Net"  NAME="SIGNAME" VALUE="{$iSigName}" IS_EDITABLE="TRUE"/>
        </xsl:otherwise>
    </xsl:choose>
    
    <VARIABLE VIEWTYPE="STATIC"    VIEWDISP="Direction" NAME="DIR" VALUE="{$iDir}"/>
    
    <xsl:if test="not($iSigIs = '__NONE__')">
        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Class" NAME="SIGIS" VALUE="{$iSigIs}"/>
    </xsl:if>
        
    <xsl:if test="not($iVecFormula = '__NONE__')">
        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Range" NAME="VECFORMULA" VALUE="{$iVecFormula}"/>
    </xsl:if>
    
    <xsl:if test="not($iSensitivity = '__NONE__')">
        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Sensitivity" NAME="SENSITIVITY" VALUE="{$iSensitivity}"/>
    </xsl:if>
</SET>
</xsl:template>

	
</xsl:stylesheet>

						    	
