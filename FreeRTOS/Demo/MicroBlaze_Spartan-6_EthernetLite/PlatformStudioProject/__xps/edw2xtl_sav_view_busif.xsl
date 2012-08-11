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
       extension-element-prefixes="exsl dyn math xlink">
           

<!--	
	================================================================================
							Generate XTeller for BIFS
	================================================================================ 
-->	

<xsl:template name="WRITE_VIEW_BIF_TREE">

    <xsl:for-each select="$G_SYS_MODS/MODULE">
    
      <xsl:variable name="modRef_" select="self::node()"/>
      <xsl:variable name="m_inst_" select="$modRef_/@INSTANCE"/>
		
	  	<xsl:element name="SET">
	       <xsl:attribute name="ID"><xsl:value-of select="@INSTANCE"/></xsl:attribute>
	       <xsl:attribute name="CLASS">MODULE</xsl:attribute>
	       
	        <xsl:choose>
                <xsl:when test="$modRef_/@POTENTIAL_INDEX">
	       			<xsl:attribute name="POTENTIAL_INDEX"><xsl:value-of select="$modRef_/@POTENTIAL_INDEX"/></xsl:attribute>
                </xsl:when>
                <xsl:when test="$modRef_/@CONNECTED_INDEX">
	       			<xsl:attribute name="CONNECTED_INDEX"><xsl:value-of select="$modRef_/@CONNECTED_INDEX"/></xsl:attribute>
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
	       
	       <!-- Write Bus Interfaces here  --> 
	       	<xsl:for-each select="$G_SYS_MODS"> <!--  To put things in the right scope for the keys below -->
	       		<xsl:variable name="m_bifs_all_"  select="key('G_MAP_ALL_BIFS', $m_inst_)"/>	
		        <xsl:for-each select="$m_bifs_all_">
		           <xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
	      			<xsl:call-template name="WRITE_VIEW_BIF_TREE_SET">
						<xsl:with-param name="iModRef" select="$modRef_"/>
						<xsl:with-param name="iBifRef" select="self::node()"/>
					</xsl:call-template>
	            </xsl:for-each> <!-- End of bus interface loop  -->
	       	</xsl:for-each>
	  </xsl:element> 
    </xsl:for-each> <!-- End module loop -->
</xsl:template>	


<xsl:template name="WRITE_VIEW_BIF_TREE_SET">
	<xsl:param name="iModRef" select="'__NONE__'"/>
	<xsl:param name="iBifRef" select="'__NONE__'"/>
	<xsl:param name="iBifCol" select="'__NONE__'"/>
	
	<xsl:element name="SET">
		<xsl:if test="not($iBifCol = '__NONE__')">
			<xsl:attribute name="RGB_FG"><xsl:value-of select="$iBifCol"/></xsl:attribute>                
		</xsl:if>
		<xsl:attribute name="ID"><xsl:value-of select="$iBifRef/@NAME"/></xsl:attribute>
		<xsl:attribute name="CLASS">BUSINTERFACE</xsl:attribute>
		
		<xsl:if test="($iBifRef/@TYPE = 'MONITOR')">
			<xsl:choose>
				<xsl:when test="($iBifRef/@IS_P2P)">
					<xsl:attribute name="IS_P2P_MONITOR">TRUE</xsl:attribute>
				</xsl:when>
				<xsl:otherwise>
					<xsl:attribute name="IS_SHARED_MONITOR">TRUE</xsl:attribute>
				</xsl:otherwise>
			</xsl:choose>
		</xsl:if>
		
		<VARIABLE VIEWTYPE="STATIC" VIEWDISP="NAME" NAME="NAME" VALUE="{$iBifRef/@NAME}"/>
        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Type" NAME="TYPE" VALUE="{$iBifRef/@TYPE}"/>
		<xsl:element name="VARIABLE">
			<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			<xsl:attribute name="VIEWDISP">Bus Standard</xsl:attribute>
			<xsl:attribute name="NAME">BUSSTD</xsl:attribute>
			<xsl:choose>
	        	<xsl:when test="($iBifRef/@BUSSTD_PSF)">
					<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSSTD_PSF"/></xsl:attribute>
	        	</xsl:when>
	        	<xsl:when test="($iBifRef/@BUSSTD)">
					<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSSTD"/></xsl:attribute>
	        	</xsl:when>
	        	<xsl:when test="($iBifRef/@BUS_STD)">
					<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUS_STD"/></xsl:attribute>
	        	</xsl:when>
           		<xsl:otherwise>
					<xsl:attribute name="VALUE">USER</xsl:attribute>
				</xsl:otherwise>
			</xsl:choose>
		</xsl:element>
		
		<xsl:choose>
			<xsl:when test="($iBifRef/@TYPE = 'INITIATOR')">
				<xsl:element name="VARIABLE">
					<xsl:attribute name="VIEWTYPE">TEXTBOX</xsl:attribute>
					<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
					<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
					<xsl:choose>
		            	<xsl:when test="(($iBifRef/@BUSNAME = '__NOC__') or ($iBifRef/@BUSNAME = '') or not($iBifRef/@BUSNAME))">
					        <xsl:variable name="def_noc_name_"><xsl:value-of select="$iModRef/@INSTANCE"/>_<xsl:value-of select="$iBifRef/@NAME"/></xsl:variable>
							<xsl:attribute name="VALUE"><xsl:value-of select="$def_noc_name_"/></xsl:attribute>
			        	</xsl:when>
		           		<xsl:otherwise>
							<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSNAME"/></xsl:attribute>
						</xsl:otherwise>
					</xsl:choose>
					<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
						<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
							<xsl:with-param name="iModRef" select="$iModRef"/>
							<xsl:with-param name="iBifRef" select="$iBifRef"/>
						</xsl:call-template>
					</xsl:if>
				</xsl:element>	             
			</xsl:when>
			
			<xsl:otherwise>
				<xsl:choose>
	                <xsl:when test="(($iBifRef/@BUSNAME = '__NOC__') or ($iBifRef/@BUSNAME = '') or not($iBifRef/@BUSNAME))">
						<xsl:element name="VARIABLE">
							<xsl:choose>
	                    		<xsl:when test="(($iBifRef/@BUSSTD = 'AXI') and ($iBifRef/@TYPE = 'SLAVE') and ($G_HAVE_XB_BUSSES = 'TRUE'))">
									<xsl:attribute name="VIEWTYPE">BUTTON</xsl:attribute>
	                    		</xsl:when>
	                    		<xsl:otherwise>
									<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
	                    		</xsl:otherwise>
							</xsl:choose>
							<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
							<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
							<xsl:attribute name="VALUE">No Connection</xsl:attribute>
							<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
								<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
									<xsl:with-param name="iModRef" select="$iModRef"/>
									<xsl:with-param name="iBifRef" select="$iBifRef"/>
								</xsl:call-template>
							</xsl:if>	
						</xsl:element>
					</xsl:when>	                    
					
                    <xsl:otherwise>
						<xsl:choose>
							<xsl:when test="(($iBifRef/@TYPE = 'MONITOR') and ($iBifRef/MONITORS/MONITOR))">
                               <xsl:variable name="monitorBif_" select="$iBifRef/MONITORS/MONITOR"/>
                               <xsl:variable name="p2pMonConn_" select="concat($monitorBif_/@INSTANCE,'.',$monitorBif_/@BUSINTERFACE)"/>
								<xsl:element name="VARIABLE">
									<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
									<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
									<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
									<xsl:attribute name="VALUE"><xsl:value-of select="$p2pMonConn_"/></xsl:attribute>
									<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
										<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
											<xsl:with-param name="iModRef" select="$iModRef"/>
											<xsl:with-param name="iBifRef" select="$iBifRef"/>
										</xsl:call-template>
									</xsl:if>
								</xsl:element>									
	                        </xsl:when>
	                        
							<xsl:when test="($iBifRef/@TYPE = 'SLAVE')">
								<xsl:element name="VARIABLE">
       								<xsl:choose>
										<xsl:when test="(($iBifRef/@BUSSTD = 'AXI') and ($G_HAVE_XB_BUSSES ='TRUE'))">
                                             <xsl:attribute name="VIEWTYPE">BUTTON</xsl:attribute>
                                         </xsl:when>
										<xsl:otherwise>
											<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
										</xsl:otherwise>
									</xsl:choose> 
                                    <xsl:attribute name="NAME">BUSNAME</xsl:attribute>
                                    <xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
                                    <xsl:choose>
                                     	<xsl:when test="$iBifRef/MASTERS/MASTER">
                                            <xsl:variable name="mastersList_"><xsl:for-each select="$iBifRef/MASTERS/MASTER"><xsl:if test="position() &gt; 1"> &amp; </xsl:if><xsl:value-of select="concat(@INSTANCE,'.',@BUSINTERFACE)"/></xsl:for-each></xsl:variable>
                                            <xsl:variable name="mastersConn_" select="concat($iBifRef/@BUSNAME,':',$mastersList_)"/>
                                             <xsl:attribute name="VALUE"><xsl:value-of select="$mastersConn_"/></xsl:attribute>
                                         </xsl:when>
                                         <xsl:otherwise>
                                             <xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSNAME"/></xsl:attribute>
                                         </xsl:otherwise>
									</xsl:choose> 
									<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
										<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
											<xsl:with-param name="iModRef" select="$iModRef"/>
											<xsl:with-param name="iBifRef" select="$iBifRef"/>
										</xsl:call-template>
									</xsl:if>									
								</xsl:element>
							</xsl:when>
							
							<xsl:otherwise>
								<xsl:element name="VARIABLE">
									<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
									<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
									<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
									<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSNAME"/></xsl:attribute>
									<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
										<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
											<xsl:with-param name="iModRef" select="$iModRef"/>
											<xsl:with-param name="iBifRef" select="$iBifRef"/>
										</xsl:call-template>
									</xsl:if>
								</xsl:element>							
							</xsl:otherwise>
						</xsl:choose>
					</xsl:otherwise>
				</xsl:choose>
			 </xsl:otherwise>
		</xsl:choose>
	</xsl:element>
</xsl:template>


<xsl:template name="WRITE_VIEW_BIF_FLAT">

    <xsl:for-each select="$G_SYS_MODS/MODULE">
    
       <xsl:sort data-type="number" select="@ROW_INDEX" order="ascending"/>
       <xsl:variable name="moduleRef_" select="self::node()"/>
       <xsl:variable name="busifsRef_">
 			<xsl:choose>
                <xsl:when test="self::node()/BUSINTERFACES"><xsl:text>$moduleRef_/BUSINTERFACES</xsl:text></xsl:when>
                <xsl:otherwise><xsl:text>$moduleRef_</xsl:text></xsl:otherwise>
			</xsl:choose>
		</xsl:variable>   
		<xsl:for-each select="dyn:evaluate($busifsRef_)/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
        	<xsl:sort data-type="number" select="@MPD_INDEX" order="ascending"/>
      		<xsl:call-template name="WRITE_VIEW_BIF_FLAT_SET">
				<xsl:with-param name="iModRef" select="$moduleRef_"/>
				<xsl:with-param name="iBifRef" select="self::node()"/>
			</xsl:call-template>
      	</xsl:for-each> <!--  End of Bus Interface Loop -->
    </xsl:for-each> <!-- End of Module loop -->
</xsl:template>

<xsl:template name="WRITE_VIEW_BIF_FLAT_SET">

	<xsl:param name="iModRef" select="'__NONE__'"/>
	<xsl:param name="iBifRef" select="'__NONE__'"/>
	<xsl:param name="iBifCol" select="'__NONE__'"/>
	
	<xsl:element name="SET">
		<xsl:if test="not($iBifCol = '__NONE__')">
			<xsl:attribute name="RGB_FG"><xsl:value-of select="$iBifCol"/></xsl:attribute>                
		</xsl:if>	
		<!-- 
		<xsl:attribute name="ID"><xsl:value-of select="$iModRef/@INSTANCE"/>.<xsl:value-of select="$iBifRef/@NAME"/></xsl:attribute>
		 -->
		<xsl:attribute name="ID"><xsl:value-of select="$iBifRef/@NAME"/></xsl:attribute>
		<xsl:attribute name="CLASS">BUSINTERFACE</xsl:attribute>

		<xsl:if test="($iBifRef/@TYPE = 'MONITOR')">
			<xsl:choose>
				<xsl:when test="($iBifRef/@IS_P2P)">
					<xsl:attribute name="IS_P2P_MONITOR">TRUE</xsl:attribute>
				</xsl:when>
				<xsl:otherwise>
					<xsl:attribute name="IS_SHARED_MONITOR">TRUE</xsl:attribute>
				</xsl:otherwise>
			</xsl:choose>
		</xsl:if>
		
		<!-- CR452579 Can only modify INSTANCE name in Hierarchal view. --> 
		<VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"      NAME="INSTANCE"  VALUE="{$iModRef/@INSTANCE}"/>
		<VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Interface" NAME="NAME"      VALUE="{$iBifRef/@NAME}"/>
		<VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"       NAME="MODTYPE"   VALUE="{$iModRef/@MODTYPE}" VIEWICON="{$iModRef/LICENSEINFO/@ICON_NAME}"/>
		<VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version"    NAME="HWVERSION" VALUE="{$iModRef/@HWVERSION}"/>
			    
	    <xsl:variable name="ipClassification_">
	        <xsl:call-template name="F_ModClass_To_IpClassification">
	            <xsl:with-param name="iModClass"  select="$iModRef/@MODCLASS"/>
	            <xsl:with-param name="iBusStd"    select="$iBifRef/@BUSSTD"/> 
	        </xsl:call-template>    
	    </xsl:variable>
			    
		<VARIABLE VIEWTYPE="STATIC"  VIEWDISP="IP Classification" NAME="IPCLASS" VALUE="{$ipClassification_}"/>
		<VARIABLE VIEWTYPE="STATIC"  VIEWDISP="Type" NAME="TYPE" VALUE="{$iBifRef/@TYPE}"/>
		
		<xsl:element name="VARIABLE">
			<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			<xsl:attribute name="VIEWDISP">Bus Standard</xsl:attribute>
			<xsl:attribute name="NAME">BUSSTD</xsl:attribute>
			<xsl:choose>
	        	<xsl:when test="($iBifRef/@BUS_STD)">
					<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUS_STD"/></xsl:attribute>
	        	</xsl:when>
	        	<xsl:when test="($iBifRef/@BUSSTD)">
					<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSSTD"/></xsl:attribute>
	        	</xsl:when>
           		<xsl:otherwise>
					<xsl:attribute name="VALUE">USER</xsl:attribute>
				</xsl:otherwise>
			</xsl:choose>
		</xsl:element>			    
		
		<xsl:choose>
			<xsl:when test="$iBifRef/@TYPE = 'INITIATOR'">
				<xsl:element name="VARIABLE">
					<xsl:attribute name="VIEWTYPE">TEXTBOX</xsl:attribute>
					<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
					<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
					<xsl:choose>
		            	<xsl:when test="(($iBifRef/@BUSNAME = '__NOC__') or ($iBifRef/@BUSNAME = '') or not($iBifRef/@BUSNAME))">
					        <xsl:variable name="def_noc_name_"><xsl:value-of select="$iModRef/@INSTANCE"/>_<xsl:value-of select="$iBifRef/@NAME"/></xsl:variable>
							<xsl:attribute name="VALUE"><xsl:value-of select="$def_noc_name_"/></xsl:attribute>
			        	</xsl:when>
		           		<xsl:otherwise>
							<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSNAME"/></xsl:attribute>
						</xsl:otherwise>
					</xsl:choose>
					<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
						<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
							<xsl:with-param name="iModRef" select="$iModRef"/>
							<xsl:with-param name="iBifRef" select="$iBifRef"/>
						</xsl:call-template>
					</xsl:if>	
				</xsl:element>		
			</xsl:when>	
			<xsl:otherwise>
	        	<xsl:choose> 
	        	
	            	<xsl:when test="(($iBifRef/@BUSNAME = '__NOC__') or ($iBifRef/@BUSNAME = '') or not($iBifRef/@BUSNAME))">
						<xsl:element name="VARIABLE">
							<xsl:choose>
	                    		<xsl:when test="(($iBifRef/@BUSSTD = 'AXI') and ($iBifRef/@TYPE = 'SLAVE') and ($G_HAVE_XB_BUSSES = 'TRUE'))">
									<xsl:attribute name="VIEWTYPE">BUTTON</xsl:attribute>
	                    		</xsl:when>
	                    		<xsl:otherwise>
									<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
	                    		</xsl:otherwise>
							</xsl:choose>
							<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
							<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
							<xsl:attribute name="VALUE">No Connection</xsl:attribute>
							<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
								<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
									<xsl:with-param name="iModRef" select="$iModRef"/>
									<xsl:with-param name="iBifRef" select="$iBifRef"/>
								</xsl:call-template>
							</xsl:if>								
						</xsl:element>
					</xsl:when>
			
					<xsl:otherwise>
	                	<xsl:choose>
	                    	<xsl:when test="(($iBifRef/@TYPE = 'MONITOR') and ($iBifRef/MONITORS/MONITOR))">
	                        	<xsl:variable name="monitorBif_" select="$iBifRef/MONITORS/MONITOR"/>
	                        	<xsl:variable name="p2pMonConn_" select="concat($monitorBif_/@INSTANCE,'.',$monitorBif_/@BUSINTERFACE)"/>
	                        	<!-- 
	                        	<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$p2pMonConn_}"/>
	                        	 -->
								<xsl:element name="VARIABLE">
									<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
									<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
									<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
									<xsl:attribute name="VALUE"><xsl:value-of select="$p2pMonConn_"/></xsl:attribute>
									<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
										<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
											<xsl:with-param name="iModRef" select="$iModRef"/>
											<xsl:with-param name="iBifRef" select="$iBifRef"/>
										</xsl:call-template>
									</xsl:if>	
								</xsl:element>		                        	
	                    	</xsl:when>
	                    
	                    	<xsl:when test="($iBifRef/@TYPE = 'SLAVE')">
	                        	<xsl:element name="VARIABLE">
	                            	<xsl:choose>
	                               		<xsl:when test="$iBifRef/@BUSSTD = 'AXI' and $G_HAVE_XB_BUSSES ='TRUE'">
	                                   		<xsl:attribute name="VIEWTYPE">BUTTON</xsl:attribute>
	                               		</xsl:when>
	                               		<xsl:otherwise>
	                                   		<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
	                               		</xsl:otherwise>
	                              	</xsl:choose> 
	                              	<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
	                              	<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
	                              	<xsl:choose>
	                                	<xsl:when test="$iBifRef/MASTERS/MASTER">
	                                  		<xsl:variable name="mastersList_"><xsl:for-each select="$iBifRef/MASTERS/MASTER"><xsl:if test="position() &gt; 1"> &amp; </xsl:if><xsl:value-of select="concat(@INSTANCE,'.',@BUSINTERFACE)"/></xsl:for-each></xsl:variable>
	                                  		<xsl:variable name="mastersConn_" select="concat($iBifRef/@BUSNAME,':',$mastersList_)"/>
	                                   		<xsl:attribute name="VALUE"><xsl:value-of select="$mastersConn_"/></xsl:attribute>
	                               		</xsl:when>
	                               		<xsl:otherwise>
	                                   		<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSNAME"/></xsl:attribute>
	                               		</xsl:otherwise>
	                              </xsl:choose> 
								  <xsl:if test="$G_ADD_CHOICES = 'TRUE'">
								  	<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
										<xsl:with-param name="iModRef" select="$iModRef"/>
										<xsl:with-param name="iBifRef" select="$iBifRef"/>
									</xsl:call-template>
								 </xsl:if>			                              
	                           </xsl:element>
	                        </xsl:when> 
	                     	<xsl:otherwise>
	                     		<!-- 
	                       		<VARIABLE VIEWTYPE="DROPDOWN"  VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$iBifRef/@BUSNAME}"/>
	                     		 -->	
								<xsl:element name="VARIABLE">
									<xsl:attribute name="VIEWTYPE">DROPDOWN</xsl:attribute>
									<xsl:attribute name="VIEWDISP">Bus Name</xsl:attribute>
									<xsl:attribute name="NAME">BUSNAME</xsl:attribute>
									<xsl:attribute name="VALUE"><xsl:value-of select="$iBifRef/@BUSNAME"/></xsl:attribute>
									<xsl:if test="$G_ADD_CHOICES = 'TRUE'">
										<xsl:call-template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">
											<xsl:with-param name="iModRef" select="$iModRef"/>
											<xsl:with-param name="iBifRef" select="$iBifRef"/>
										</xsl:call-template>
									</xsl:if>	
								</xsl:element>		                       		
	                     	</xsl:otherwise>
	                   </xsl:choose>
	            </xsl:otherwise>
	        </xsl:choose>
		</xsl:otherwise>
	</xsl:choose>			            
 </xsl:element>  
</xsl:template>

<xsl:template name="WRITE_VIEW_BIF_BUSNAME_CHOICES">

	<xsl:param name="iModRef" select="None"/>
	<xsl:param name="iBifRef" select="None"/>
	
	<xsl:variable name="b_bus_"      select="$iBifRef/@BUSNAME"/>
	<xsl:variable name="b_name_"     select="$iBifRef/@NAME"/>
	<xsl:variable name="b_type_"     select="$iBifRef/@TYPE"/>
	<xsl:variable name="b_bstd_"     select="$iBifRef/@BUSSTD"/>
	<xsl:variable name="b_bstd_psf_" select="$iBifRef/@BUSSTD_PSF"/>
	<xsl:variable name="b_protocol_" select="$iBifRef/@PROTOCOL"/>
	
	<xsl:element name="CHOICES">
		<xsl:choose>
			<xsl:when test="($b_type_ = 'INITIATOR')">
				<xsl:variable name="initiator_busName_">
	    			<xsl:choose>
	    				<xsl:when test="($b_bus_ = '__NOC__')"><xsl:value-of select="concat($iModRef/@INSTANCE,'_',$b_name_)"/></xsl:when>	
	   					<xsl:otherwise><xsl:value-of select="$b_bus_"/></xsl:otherwise>
	   				</xsl:choose>
   				</xsl:variable>
				<CHOICE NAME="{$initiator_busName_}"/>
   			</xsl:when>	
   				
			<xsl:when test="(($b_type_ = 'MASTER') or ($b_type_ = 'SLAVE') or ($b_type_ = 'MASTER_SLAVE'))">
				<CHOICE NAME="No Connection"/>
    			<xsl:for-each select="$G_SYS_MODS"> <!--  To set correct scope for KEY functions below -->
					<xsl:if test="not(($b_bstd_ = 'AXI') and ($b_type_ = 'SLAVE'))">
						<CHOICE NAME="New Connection"/>
					</xsl:if>
    				<xsl:for-each select="key('G_MAP_BUSSES',$b_bstd_)">
    					<xsl:variable name="busName_" select="@INSTANCE"/>	
    					<xsl:choose>
							<!-- CR#590473 This was setting wrong choices filled up-->
    						<!--xsl:when test="(($b_type_ = 'SLAVE') and (@IS_CROSSBAR) and $iBifRef/@PROTOCOL)">
   								<xsl:for-each select="key('G_MAP_MST_BIFS',$busName_)[(@PROTOCOL = $b_protocol_)]">
   									<xsl:variable name="bifName_" select="@NAME"/>	
   									<xsl:variable name="insName_" select="../../@INSTANCE"/>	
   									<xsl:variable name="xb_slave_busName_" select="concat($busName_,':',$insName_,'.',$bifName_)"/>
									<CHOICE NAME="{$xb_slave_busName_}"/>
   								</xsl:for-each>
    						</xsl:when-->
    						<xsl:when test="($b_type_ = 'SLAVE') and (@IS_CROSSBAR)">
   								<xsl:for-each select="key('G_MAP_MST_BIFS',$busName_)">
   									<xsl:variable name="bifName_" select="@NAME"/>	
   									<xsl:variable name="insName_" select="../../@INSTANCE"/>	
   									<xsl:variable name="xb_slave_busName_" select="concat($busName_,':',$insName_,'.',$bifName_)"/>
									<CHOICE NAME="{$xb_slave_busName_}"/>
   								</xsl:for-each>
    						</xsl:when>    						
    						<xsl:otherwise>
								<CHOICE NAME="{$busName_}"/>
    						</xsl:otherwise>
    					</xsl:choose>
    				</xsl:for-each>
    			</xsl:for-each>	
			</xsl:when>
			
			<xsl:when test="($b_type_ = 'TARGET')">
				<CHOICE NAME="No Connection"/>
				<xsl:for-each select="$G_SYS_MODS"> <!--  To set correct scope for KEY functions below -->
					<xsl:variable name="use_bstd_"> 
						<xsl:choose>
							<xsl:when test="(($b_bstd_ = 'AXIS') or ($b_bstd_ = 'XIL'))">
								<xsl:value-of select="$b_bstd_psf_"/>
							</xsl:when>	
							<xsl:otherwise>
								<xsl:value-of select="$b_bstd_"/>
							</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>
					<xsl:choose>
						<xsl:when test="$iBifRef/@PROTOCOL">
							<xsl:for-each select="key('G_MAP_P2P_BIFS',$use_bstd_)[(@TYPE = 'INITIATOR') and (@PROTOCOL = $b_protocol_)]">
			   					<xsl:variable name="busName_" select="@BUSNAME"/>
			   					<xsl:choose>
			   						<xsl:when test="($busName_ = '__NOC__')">
			   							<xsl:variable name="bifName_" select="@NAME"/>
										<xsl:variable name="insName_" select="../../@INSTANCE"/>	
			  							<xsl:variable name="initiator_busName_" select="concat($insName_,'_',$bifName_)"/>
										<CHOICE NAME="{$initiator_busName_}"/>
			   						</xsl:when>
			   						<xsl:otherwise>
										<CHOICE NAME="{$busName_}"/>
			   						</xsl:otherwise>
			   					</xsl:choose>
			    			</xsl:for-each>						
		    			</xsl:when>
		    			<xsl:otherwise>
							<xsl:for-each select="key('G_MAP_P2P_BIFS',$use_bstd_)[(@TYPE = 'INITIATOR')]">
			   					<xsl:variable name="busName_" select="@BUSNAME"/>
			   					<xsl:choose>
			   						<xsl:when test="($busName_ = '__NOC__')">
			   							<xsl:variable name="bifName_" select="@NAME"/>
										<xsl:variable name="insName_" select="../../@INSTANCE"/>	
			  							<xsl:variable name="initiator_busName_" select="concat($insName_,'_',$bifName_)"/>
										<CHOICE NAME="{$initiator_busName_}"/>
			   						</xsl:when>
			   						<xsl:otherwise>
										<CHOICE NAME="{$busName_}"/>
			   						</xsl:otherwise>
			   					</xsl:choose>
		    				</xsl:for-each>
		    			</xsl:otherwise>	
					</xsl:choose>
				</xsl:for-each>
			</xsl:when>
			
			<xsl:when test="($b_type_ = 'MONITOR')">			
				<CHOICE NAME="No Connection"/>
    			<xsl:for-each select="$G_SYS_MODS"> <!--  To set correct scope for KEY functions below -->
    				<xsl:choose>
    					<xsl:when test="($iBifRef/@IS_P2P = 'TRUE')">
			    			<xsl:for-each select="$G_SYS_MODS"> <!--  To set correct scope for KEY functions below -->
								<xsl:variable name="use_bstd_"> 
									<xsl:choose>
										<xsl:when test="(($b_bstd_ = 'AXIS') or ($b_bstd_ = 'XIL'))">
											<xsl:value-of select="$b_bstd_psf_"/>
										</xsl:when>	
										<xsl:otherwise>
											<xsl:value-of select="$b_bstd_"/>
										</xsl:otherwise>
									</xsl:choose>
								</xsl:variable>
								<!--  <xsl:message>monitor p2p <xsl:value-of select="count(key('G_MAP_P2P_BIFS',$use_bstd_)[(@TYPE = 'INITIATOR')])"/> </xsl:message> -->
								<xsl:for-each select="key('G_MAP_P2P_BIFS',$use_bstd_)[(@TYPE = 'INITIATOR')]">
				   					<xsl:variable name="busName_" select="@BUSNAME"/>
				   					<xsl:choose>
				   						<xsl:when test="($busName_ = '__NOC__')">
				   							<xsl:variable name="bifName_" select="@NAME"/>
											<xsl:variable name="insName_" select="../../@INSTANCE"/>	
				  							<xsl:variable name="initiator_busName_" select="concat($insName_,'_',$bifName_)"/>
											<CHOICE NAME="{$initiator_busName_}"/>
				   						</xsl:when>
				   						<xsl:otherwise>
											<CHOICE NAME="{$busName_}"/>
				   						</xsl:otherwise>
				   					</xsl:choose>
				    			</xsl:for-each>				
							</xsl:for-each>	
    					</xsl:when>	
    					<xsl:otherwise>
		    				<xsl:for-each select="key('G_MAP_BUSSES',$b_bstd_)">
		    					<xsl:variable name="busName_" select="@INSTANCE"/>	
		    					<xsl:choose>
		    						<xsl:when test="(@IS_CROSSBAR or ($b_bstd_ = 'AXI'))">
		   								<xsl:for-each select="key('G_MAP_MOS_BIFS',$busName_)">
		   									<xsl:variable name="bifName_" select="@NAME"/>	
		   									<xsl:variable name="insName_" select="../../@INSTANCE"/>	
		   									<!-- 
		   									<xsl:variable name="xb_moni_busName_" select="concat($busName_,':',$insName_,'.',$bifName_)"/>
		   									 -->
		   									<xsl:variable name="xb_moni_busName_" select="concat($insName_,'.',$bifName_)"/>
											<CHOICE NAME="{$xb_moni_busName_}"/>
		   								</xsl:for-each>
		    						</xsl:when>
		    						<xsl:otherwise>
										<CHOICE NAME="{$busName_}"/>
		    						</xsl:otherwise>
		    					</xsl:choose>
		    				</xsl:for-each>
    					</xsl:otherwise>

    				</xsl:choose>
    			</xsl:for-each>					
			</xsl:when>
		</xsl:choose>
	</xsl:element>
	
</xsl:template>	
		 
		 

</xsl:stylesheet>

