<?xml version="1.0" encoding="iso-8859-1" ?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

    <xsl:template match="datasheet">
        <html>
            <head>
                <xsl:call-template name="css"/>
            </head>
            <body>
                <a name="top"/>
                <div>
                    <xsl:apply-templates select="header"/>
                </div>
                <div class="dsheet">
                    <div>
                        <xsl:apply-templates select="project-settings"/>
                    </div>
                    <div>
                        <div class="header">Table of Contents</div>
                        <div class="content" >
                            <a href="#generated_files">Generated Files</a>
                            <br/>
                            <a href="#ios">IO's</a>
                            <br/>
                            <a href="#cores">Hardware Instances</a>
                            <br/>
                            <a href="#firmware_cores">Firmware</a>
                            <br/>
                            <a href="#memmap">Memory Map</a>
                            <!-- <a href="{header}_MemoryMap.xml" >Memory Map</a> -->
                        </div>
                    </div>

                    <!-- ======= Generated File's ======= -->
                    <div>
                        <p>
                            <a name="generated_files"/>
                            <div class="header">Generated Files</div>
                        </p>
                        <xsl:call-template name="generated_files"/>
                    </div>

                    <!-- ======= IO's ======= -->
                    <div>
                        <p>
                            <a name="ios"/>
                            <div class="header">IO's</div>
                        </p>
                        <xsl:call-template name="ios"/>
                    </div>

                    <br/>
                    <!-- ===== CORES ====== -->
                    <div>
                        <a name="cores"/>
                        <div class="header">
                            Cores
                        </div>
                        <xsl:call-template name="cores"/>

                    </div>

                    <!-- ======= Firwmare ======= -->
                    <div>
                        <p>
                            <a name="firmware_cores"/>
                            <div class="header">Firmware</div>
                        </p>
                        <xsl:call-template name="firmware_cores"/>
                    </div>

                    <!-- ===== MEMORY MAP ====== -->
                    <div>
                        <a name="memmap"/>
                        <div class="header">
                            Memory Map
                        </div>
                        <xsl:apply-templates select="memorysystem"/>
                    </div>

                </div>
            </body>
        </html>
    </xsl:template>



    <xsl:template match="header">
        <div class="title">
            <h1>
                Data Sheet: <xsl:value-of select="."/>
            </h1>
            <!-- ======= IO's ======= 
      <div class="copyright">
        Copyright 2008 Actel Corporation
      </div>
	  -->
        </div>
    </xsl:template>

    <xsl:template match="project-settings">
        <div class="header">Project Settings</div>

        <div class="content">
            <table border="0" cellspacing="4">
                <tr>
                    <td>
                        <b>FAM: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="fam"/>
                    </td>
                </tr>
                <tr>
                    <td>
                        <b>Die: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="die"/>
                    </td>
                </tr>
                <tr>
                    <td>
                        <b>Package: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="package"/>
                    </td>
                </tr>

                <tr>
                    <td>
                        <b>Speed Grade: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="speed-grade"/>
                    </td>
                </tr>

                <tr>
                    <td>
                        <b>Voltage: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="voltage"/>
                    </td>
                </tr>

                <tr>
                    <td>
                        <b>HDL: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="hdl-type"/>
                    </td>
                </tr>

                <tr>
                    <td>
                        <b>Project Description: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="project-description"/>
                    </td>
                </tr>

                <tr>
                    <td>
                        <b>Location: </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="location"/>
                    </td>
                </tr>

                <tr>
                    <td>
                        <b>State (Time): </b>
                    </td>
                    <td>
                        <xsl:apply-templates select="state"/>
                    </td>
                </tr>
            </table>
        </div>
        <br/>
    </xsl:template>

    <!-- /////////////////////////////////////////////////////////  -->

    <xsl:template name="generated_files">
        <div class="content">
            <xsl:for-each select="fileset">
                <b>File set:  </b>
                <xsl:value-of select="name"/>
                <br/>

                <xsl:for-each select="file">
                    <li>
                        <xsl:value-of select="."/>
                    </li>
                </xsl:for-each>
                <br/>
            </xsl:for-each>
        </div>
        <xsl:call-template name="top-link"/>
    </xsl:template>


    <!-- /////////////////////////////////////////////////////////  -->

    <xsl:template name="print-ios">
        <td>
            <xsl:apply-templates select="port-name"/>
        </td>
        <td>
            <xsl:apply-templates select="direction"/>
        </td>
        <td>
            <xsl:apply-templates select="pin-number"/>
        </td>
        <td>
            <xsl:apply-templates select="io-standard"/>
        </td>
    </xsl:template>

    <xsl:template name="ios">
        <xsl:choose>
            <xsl:when test="count(io) &gt; 0">
                <table class="ios"  align="center"  border="1" width="75%" cellspacing="0" cellpadding="4">
                    <tr>
                        <th>
                            Port Name
                        </th>
                        <th>
                            Direction
                        </th>
                        <th>
                            Pin
                        </th>
                        <th>
                            I/O Standard
                        </th>
                    </tr>
                    <xsl:for-each select="io">
                        <tr>
                            <xsl:call-template name="print-ios"/>
                        </tr>
                    </xsl:for-each>
                </table>
            </xsl:when>
            <xsl:otherwise>
                <i>No IO's </i>
                <br/>
                <br/>
            </xsl:otherwise>
        </xsl:choose>
        <xsl:call-template name="top-link"/>
    </xsl:template>


    <!-- /////////////////////////////////////////////////////////  -->

    <xsl:template name="firmware_cores">
        <xsl:choose>
            <xsl:when test="count(firmware_core) &gt; 0">
                <!-- Core TOC -->
                <div class="content">
                    <b>Software IDE: </b>
                    <xsl:value-of select="/datasheet/project-settings/swide-toolchain"/>
                    <br/>
                    <br/>

                    <span class="instances">Drivers:</span>
                    <br/>
                    <xsl:for-each select="firmware_core">
                        <a href="#{core-name}">
                            <xsl:value-of select="core-name"/>
                        </a>

                        <br/>
                    </xsl:for-each>
                    <br/>
                    <div class="toplinks">
                        <xsl:call-template name="top-link"/>
                    </div>
                </div>

                <xsl:for-each select="firmware_core">
                    <div class="content">
                        <!-- Core TOC -->
                        <a name="{core-name}"/>

                        <table class="cores" width="97%" border="0" cellspacing="0" cellpadding="14">
                            <!--border="1"  cellspacing="0" cellpadding="14"> -->
                            <xsl:choose>

                                <xsl:when test='@type="FirmWareModule"'>
                                    <xsl:call-template name="print-cores-spirit"/>
                                </xsl:when>

                            </xsl:choose>

                        </table>
                        <div class="toplinks">
                            <a href="#cores">instance list</a>, <xsl:call-template name="top-link"/>
                        </div>
                    </div>
                    <br/>
                </xsl:for-each>
                <br/>
            </xsl:when>
            <xsl:otherwise>
                <br/>
                <i>No Firmware Generated.  Design may not contain any processor subsystems, or firmware have not been downloaded to your vault</i>
                <br/>
                <br/>
                <xsl:call-template name="top-link"/>
                <br/>
                <br/>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>



    <!-- /////////////////////////////////////////////////////////  -->

    <xsl:template name="cores">
        <xsl:choose>

            <xsl:when test="count(core) &gt; 0">
                <!-- Core TOC -->
                <div class="content">
                    <span class="instances">Instances:</span>
                    <br/>
                    <xsl:for-each select="core">
                        <a href="#{core-name}">
                            <xsl:value-of select="core-name"/>
                        </a>

                        <br/>
                    </xsl:for-each>
                    <br/>
                    <div class="toplinks">
                        <xsl:call-template name="top-link"/>
                    </div>
                </div>

                <xsl:for-each select="core">
                    <div class="content">
                        <!-- Core TOC -->
                        <a name="{core-name}"/>

                        <table class="cores" width="97%" border="0" cellspacing="0" cellpadding="14">
                            <!--border="1"  cellspacing="0" cellpadding="14"> -->
                            <xsl:choose>
                                <xsl:when test='@type="ComponentModule"'>
                                    <xsl:call-template name="print-cores-comp"/>
                                </xsl:when>
                                <xsl:when test='@type="SpiritModule"'>
                                    <xsl:call-template name="print-cores-spirit"/>
                                </xsl:when>
                                <xsl:when test='@type="AdlibModule"'>
                                    <xsl:call-template name="print-cores-adlib"/>
                                </xsl:when>
                                <xsl:when test='@type="HdlModule"'>
                                    <xsl:call-template name="print-cores-hdl"/>
                                </xsl:when>
                            </xsl:choose>

                        </table>
                        <div class="toplinks">
                            <a href="#cores">instance list</a>, <xsl:call-template name="top-link"/>
                        </div>
                    </div>
                    <br/>
                </xsl:for-each>
                <br/>
            </xsl:when>
            <xsl:otherwise>
                <br/>
                <i>No Instances</i>
                <br/>
                <br/>
                <xsl:call-template name="top-link"/>
                <br/>
                <br/>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>

    <xsl:template name="print-cores-comp">
        <tr>
            <td>
                <table border="0">
                    <xsl:call-template name="print-cores"/>
                    <tr>
                        <td>
                            <b>Type: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-exttype"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Location: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-location"/>
                        </td>
                    </tr>
                </table>
            </td>
        </tr>
    </xsl:template>

    <xsl:template name="print-cores-spirit">
        <tr>
            <td>
                <table border="0">
                    <xsl:call-template name="print-cores"/>
                    <tr>
                        <td>
                            <b>Type: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-exttype"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Vendor: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-vendor"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Library: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-lib"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Core Name: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-intname"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Version: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-ver"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Description: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-desc"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>Parameters: </b>
                        </td>
                        <td>
                            <xsl:call-template name="print-spirit-params"/>
                        </td>
                    </tr>
                </table>
            </td>
        </tr>
    </xsl:template>

    <xsl:template name="print-spirit-params" >
        <xsl:if test="count(core-param) > 0">
            <div style="background-color: #F0F0F0; " >
                <br/>
                <table>
                    <!-- <tr>
            <th>
              Name
            </th>
            <th>
              Value
            </th>
          </tr> -->
                    <xsl:for-each select="core-param">
                        <xsl:call-template name="print-core-params"/>
                    </xsl:for-each>
                </table>
            </div>
        </xsl:if>
        <xsl:if test="count(core-param) &lt; 1">
            <i>No parameters</i>
        </xsl:if>
    </xsl:template>

    <xsl:template name="print-cores-adlib">
        <tr>
            <td>
                <table border="0">
                    <xsl:call-template name="print-cores"/>
                    <tr>
                        <td>
                            <b>Cell Type: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-exttype"/>
                        </td>
                    </tr>
                </table>

            </td>
        </tr>
    </xsl:template>

    <xsl:template name="print-cores-hdl">
        <tr>
            <td>
                <table border="0">
                    <xsl:call-template name="print-cores"/>
                    <tr>
                        <td>
                            <b>Module Name: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-exttype"/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <b>HDL File: </b>
                        </td>
                        <td>
                            <xsl:apply-templates select="core-location"/>
                        </td>
                    </tr>
                </table>
            </td>
        </tr>
    </xsl:template>

    <xsl:template name="print-cores">
        <tr>
            <td width="200">
                <b>Instance Name: </b>
            </td>
            <td>
                <xsl:apply-templates select="core-name"/>
            </td>
        </tr>
    </xsl:template>

    <xsl:template name="print-core-params">
        <tr>
            <td>
                <b class="params-name">
                    <xsl:apply-templates select="param-hdlname"/> [ <xsl:apply-templates select="param-name"/> ]
                </b>
            </td>
            <td>
                <xsl:apply-templates select="param-hdlvalue"/> [ <xsl:apply-templates select="param-value"/> ]
            </td>
        </tr>
    </xsl:template>




    <!--/////////////////////////////////////////////////////////-->

    <xsl:template match="port-name|direction|pin-number|io-standard">
        <xsl:value-of select="."/>
    </xsl:template >

    <xsl:template match="core-name|core-type|core-exttype">
        <xsl:value-of select="."/>
    </xsl:template >

    <xsl:template match="core-vendor|core-lib|core-intname|core-ver|core-desc">
        <xsl:value-of select="."/>
    </xsl:template >

    <xsl:template match="core-location">
        <xsl:value-of select="."/>
    </xsl:template >

    <xsl:template match="fam|die|package|hdl-type|location|state">
        <xsl:value-of select="."/>
    </xsl:template >

    <xsl:template match="param-name|param-value|param-tag|param-hdlname|param-hdlvalue">
        <xsl:value-of select="."/>
    </xsl:template >


    <xsl:template name="top-link">
        <a href="#top">top of page</a>
    </xsl:template>



    <!--=============================MEMORY MAP===================================-->

    <xsl:template match="memorysystem">

        <div class="content">
            <xsl:apply-templates select="description"/>
        </div>
        <div>
            <xsl:apply-templates select="subsystems"/>
        </div>

    </xsl:template>


    <xsl:template match="subsystems">

        <xsl:for-each select="subsystem">
            <li>
                <div class="content">
                    <a href="#{name} Memory Map">
                        <xsl:value-of select="node()"/>
                    </a>
                </div>
            </li>
        </xsl:for-each>

        <div class="content">
            <div class="toplinks">
                <xsl:call-template name="top-link"/>
            </div>
        </div>
        <br/>

        <hr></hr>
        <xsl:apply-templates select="subsystem"/>

    </xsl:template>

    <xsl:template match="subsystem">
        <div class="content">
            <h2>
                <a name="{name} Memory Map">
                    <xsl:value-of select="name"/>
                </a> Subsystem
            </h2>
            Master(s) on this bus:
            <xsl:apply-templates select="master"/>
            <br></br><br></br>

            <xsl:apply-templates select="addressNames" />
            <a href="#memmap">subsystem list</a>,
            <xsl:call-template name="top-link"/>

            <br/><br/>
            <hr></hr>
            <xsl:apply-templates select="slave"/>
        </div>
    </xsl:template>

    <xsl:template match="title">
        <span style="color:#000000">
            <xsl:value-of select="text()"/>
        </span>
    </xsl:template>

    <xsl:template match="description">
        <xsl:value-of select="text()"/>
    </xsl:template>

    <xsl:template match="master">
        <li>
            <div class="content">
                <xsl:value-of select="text()"/>
            </div>
        </li>
    </xsl:template>

    <xsl:template match="addressNames">
        <table class="regs" border="1" cellspace="0" cellpadding="10"  align="center" >
            <xsl:if test="count = 1">
                <tr bgcolor="#aaaacc">
                    <th rowspan="1"></th>
                    <th colspan="2">Address Range</th>
                </tr>
            </xsl:if>
            <xsl:if test="count &gt; 1">
                <tr bgcolor="#aaaacc">
                    <th rowspan="2"></th>
                    <th colspan="2">Address Range</th>
                </tr>
                <tr>
                    <xsl:for-each select="name">
                        <th bgcolor="#aaaacc">
                            <xsl:value-of select="text()"/>
                        </th>
                    </xsl:for-each>
                </tr>
            </xsl:if>

            <xsl:for-each select="../slave">
                <tr>
                    <th cellspace="0" colspan="1">
                        <b>
                            <a class="toplinks" href="#{name}_{memoryMap/name} Register">
                                <xsl:value-of select="name"/> : <xsl:value-of select="memoryMap/name"/>
                            </a>
                        </b>
                    </th>
                    <xsl:for-each select="fullAddressSpace">
                        <td align="center">
                            <xsl:value-of select="text()"/>
                        </td>
                    </xsl:for-each>
                </tr>
            </xsl:for-each>

        </table>
    </xsl:template>

    <xsl:template match="slave">
        <div class="content">
            <h3>
                <a name="{name}_{memoryMap/name} Register">
                    <xsl:value-of select="name"/> : <xsl:value-of select="memoryMap/name"/> Memory Map [
                    <xsl:value-of select="fullAddressSpace"/> ]
                </a>
            </h3>
        </div>
        <div class="mmrange">

            <i>range: </i>
            <xsl:apply-templates select="range"/>

        </div>
        <xsl:if test="memoryMap/addressBlock/register">
            <xsl:apply-templates select="memoryMap/addressBlock"/>
        </xsl:if>
        <a class="toplinks" href="#{../name} Memory Map">
            back to <xsl:value-of select="../name"/> Memory Map
        </a>
        <br/>
        <br/>
        <hr></hr>
    </xsl:template>

    <xsl:template match="addressBlock">
        <table class="regs" border="2" cellspace="0" cellpadding="4" align="center">
            <tr bgcolor="#aaaacc">
                <th>Address</th>
                <th>Name</th>
                <th>R/W</th>
                <th>Width</th>
                <th>Reset Value</th>
                <th>Description</th>
            </tr>
            <xsl:for-each select="register">
                <tr>
                    <td align="center" nowrap="true">
                        <xsl:value-of select="absoluteAddress"/>
                    </td>
                    <xsl:choose>
                        <xsl:when test="field">
                            <td align="center">
                                <a class="toplinks" href="#{../../../name}_{name}">
                                    <xsl:value-of select="name"/>
                                </a>
                            </td>
                        </xsl:when>
                        <xsl:otherwise>
                            <td align="center">
                                <xsl:value-of select="name"/>
                            </td>
                        </xsl:otherwise>
                    </xsl:choose>
                    <td align="center" nowrap="true">
                        <xsl:value-of select="access"/>
                    </td>
                    <td align="center">
                        <xsl:value-of select="size"/>
                    </td>
                    <td align="center">
                        <xsl:value-of select="resetValue"/>
                    </td>
                    <td align="left">
                        <xsl:value-of select="description"/>
                    </td>
                </tr>
            </xsl:for-each>
        </table>

        <xsl:if test="register/field">
            <a class="toplinks" href="#{../../../name} Memory Map">
                back to <xsl:value-of select="../../../name"/> Memory Map
            </a>
            <xsl:for-each select="register">
                <div class="content">
                    <h4>
                        <a class="register-details" name="{../../../name}_{name}">
                            <xsl:value-of select="name"/> register details [ <xsl:value-of select="absoluteAddress"/> ] :
                        </a>
                    </h4>
                </div>
                <div class="regwidth">

                    <i>width: </i>
                    <xsl:apply-templates select="size"/>-bit

                </div>

                <table class="regs" border="2" cellspace="0" cellpadding="4" align="center" >
                    <tr bgcolor="#aaaacc">
                        <th align="left">Bit Number</th>
                        <th>Name</th>
                        <th>R/W</th>
                        <th>Description</th>
                    </tr>
                    <xsl:for-each select="field">
                        <tr>
                            <td align="left">
                                <xsl:value-of select="bitNumber"/>
                            </td>
                            <td align="center">
                                <xsl:value-of select="name"/>
                            </td>
                            <td align="center" nowrap="true">
                                <xsl:value-of select="access"/>
                            </td>
                            <td align="left">
                                <xsl:value-of select="description"/>
                            </td>
                        </tr>
                    </xsl:for-each>
                </table>

                <a class="toplinks" href="#{../../../name}_{../../../memoryMap/name} Register">
                    back to <xsl:value-of select="../../../name"/> Registers
                </a>
                <br/>
                <br/>
            </xsl:for-each>
            <br/>
            <br/>
        </xsl:if>

    </xsl:template>

    <xsl:template match="range">
        <xsl:value-of select="."/>
    </xsl:template >

    <!--==========================END MEMORY MAP===================================-->



    <!--============================= CSS ===================================-->
    <xsl:template name="css">
        <style>

            html
            {
            background-color:darkgray;
            }

            body
            {
            font-family:arial;
            font-size: 11pt;
            text-align:center;
            }


            th
            {
            background-color: #F0F0F0;
            }

            table.cores
            {
            background-color: #F0F0F0;
            border-color: #B0B0B0;
            border-style:solid;
            border-width:1px;
            }

            table.cores td
            {
            vertical-align:top;
            }

            table.regs,
            table.ios
            {
            border-color: #B0B0B0;
            border-style:solid;
            border-width:1px;
            border-spacing:0px;
            border-collapse:collapse;
            width=75%;
            font-family:couriernew;
            font-size: 11pt;
            }

            table.regs th
            table.ios th
            {
            border-color: #B0B0B0;
            border-width:1px;
            color: darkslategray;
            font-weight:bold;
            }


            table.ios td
            {
            text-align:center;
            }


            table.params
            {
            border-color: #D0D0D0;
            border-style:solid;
            border-width:0px;
            border-spacing:0px;
            border-collapse:collapse;
            }


            table.params th
            {
            border-color: #D0D0D0;
            border-width:1px;
            color: black;
            font-weight:bold;
            }

            table.params td
            {
            text-align:center;
            }

            b.params-name
            {
            color: #505050   ;

            }


            div.header
            {
            padding-top: 7px;
            padding-bottom: 7px;
            color:#003399;
            background-color: #D0D0D0;
            width=100%;
            font-family:arial;
            font-size:14pt;
            font-weight: bold;
            text-align: center;
            }

            div.title
            {
            padding-top: 30px;
            margin: auto;
            color:#D0D0D0;
            background-color:#003399 ;

            text-align: center;
            width: 1000px;
            padding-left:30px;
            padding-right:30px;
            }

            div.dsheet
            {
            width: 1000px;
            margin: auto;
            text-align: left

            color:#003399;
            background-color: white;

            padding-top: 30px;
            padding-bottom: 30px;
            padding-left:30px;
            padding-right:30px;
            }

            div.content
            {
            padding-top: 10px;
            padding-left:10px;
            padding-right:10px;

            text-align: left;
            font-size: 13pt;
            font-weight: normal;
            }

            div.copyright
            {
            text-align:right;
            font-size:9pt;
            font-style:italic;
            font-weight:normal;
            }

            div.links
            {
            text-align:left;
            }

            b
            {
            color:darkslategray
            }

            hr
            {
            width=100%;
            }

            .instances
            {
            font-size:14pt;
            text-align:left;
            }

            .toplinks
            {
            font-size:10pt;
            text-align:left;
            }

            .register-details
            {
            text-indent:20px;
            }

            .mmrange
            {
            text-indent:10px;
            font-size:11pt;
            text-align: left;
            padding-bottom: 20px;

            }

            .regwidth
            {
            text-indent:24pt;
            font-size:11pt;
            text-align: left;
            padding-bottom: 20px;
            }

        </style>

        <!--============================= END CSS ===================================-->
    </xsl:template>

</xsl:stylesheet>
