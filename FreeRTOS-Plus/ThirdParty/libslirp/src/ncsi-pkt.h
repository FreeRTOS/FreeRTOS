/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright Gavin Shan, IBM Corporation 2016.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above
 * copyright notice, this list of conditions and the following
 * disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following
 * disclaimer in the documentation and/or other materials provided
 * with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef NCSI_PKT_H
#define NCSI_PKT_H

/* from linux/net/ncsi/ncsi-pkt.h */
#define __be32 uint32_t
#define __be16 uint16_t

SLIRP_PACKED_BEGIN
struct ncsi_pkt_hdr {
    unsigned char mc_id; /* Management controller ID */
    unsigned char revision; /* NCSI version - 0x01      */
    unsigned char reserved; /* Reserved                 */
    unsigned char id; /* Packet sequence number   */
    unsigned char type; /* Packet type              */
    unsigned char channel; /* Network controller ID    */
    __be16 length; /* Payload length           */
    __be32 reserved1[2]; /* Reserved                 */
} SLIRP_PACKED_END;

SLIRP_PACKED_BEGIN
struct ncsi_cmd_pkt_hdr {
    struct ncsi_pkt_hdr common; /* Common NCSI packet header */
} SLIRP_PACKED_END;

SLIRP_PACKED_BEGIN
struct ncsi_rsp_pkt_hdr {
    struct ncsi_pkt_hdr common; /* Common NCSI packet header */
    __be16 code; /* Response code             */
    __be16 reason; /* Response reason           */
} SLIRP_PACKED_END;

SLIRP_PACKED_BEGIN
struct ncsi_aen_pkt_hdr {
    struct ncsi_pkt_hdr common; /* Common NCSI packet header */
    unsigned char reserved2[3]; /* Reserved                  */
    unsigned char type; /* AEN packet type           */
} SLIRP_PACKED_END;

/* NCSI common command packet */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header */
    __be32 checksum; /* Checksum       */
    unsigned char pad[26];
} SLIRP_PACKED_END;

SLIRP_PACKED_BEGIN
struct ncsi_rsp_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header */
    __be32 checksum; /* Checksum        */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* Select Package */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_sp_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header */
    unsigned char reserved[3]; /* Reserved       */
    unsigned char hw_arbitration; /* HW arbitration */
    __be32 checksum; /* Checksum       */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* Disable Channel */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_dc_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header  */
    unsigned char reserved[3]; /* Reserved        */
    unsigned char ald; /* Allow link down */
    __be32 checksum; /* Checksum        */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* Reset Channel */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_rc_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header */
    __be32 reserved; /* Reserved       */
    __be32 checksum; /* Checksum       */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* AEN Enable */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_ae_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header   */
    unsigned char reserved[3]; /* Reserved         */
    unsigned char mc_id; /* MC ID            */
    __be32 mode; /* AEN working mode */
    __be32 checksum; /* Checksum         */
    unsigned char pad[18];
} SLIRP_PACKED_END;

/* Set Link */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_sl_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header    */
    __be32 mode; /* Link working mode */
    __be32 oem_mode; /* OEM link mode     */
    __be32 checksum; /* Checksum          */
    unsigned char pad[18];
} SLIRP_PACKED_END;

/* Set VLAN Filter */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_svf_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header    */
    __be16 reserved; /* Reserved          */
    __be16 vlan; /* VLAN ID           */
    __be16 reserved1; /* Reserved          */
    unsigned char index; /* VLAN table index  */
    unsigned char enable; /* Enable or disable */
    __be32 checksum; /* Checksum          */
    unsigned char pad[14];
} SLIRP_PACKED_END;

/* Enable VLAN */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_ev_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header   */
    unsigned char reserved[3]; /* Reserved         */
    unsigned char mode; /* VLAN filter mode */
    __be32 checksum; /* Checksum         */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* Set MAC Address */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_sma_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header          */
    unsigned char mac[6]; /* MAC address             */
    unsigned char index; /* MAC table index         */
    unsigned char at_e; /* Addr type and operation */
    __be32 checksum; /* Checksum                */
    unsigned char pad[18];
} SLIRP_PACKED_END;

/* Enable Broadcast Filter */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_ebf_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header */
    __be32 mode; /* Filter mode    */
    __be32 checksum; /* Checksum       */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* Enable Global Multicast Filter */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_egmf_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header */
    __be32 mode; /* Global MC mode */
    __be32 checksum; /* Checksum       */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* Set NCSI Flow Control */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_snfc_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header    */
    unsigned char reserved[3]; /* Reserved          */
    unsigned char mode; /* Flow control mode */
    __be32 checksum; /* Checksum          */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* OEM Request Command as per NCSI Specification */
SLIRP_PACKED_BEGIN
struct ncsi_cmd_oem_pkt {
    struct ncsi_cmd_pkt_hdr cmd; /* Command header    */
    __be32 mfr_id; /* Manufacture ID    */
    unsigned char data[]; /* OEM Payload Data  */
} SLIRP_PACKED_END;

/* OEM Response Packet as per NCSI Specification */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_oem_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Command header    */
    __be32 mfr_id; /* Manufacture ID    */
    unsigned char data[]; /* Payload data      */
} SLIRP_PACKED_END;

/* Mellanox Response Data */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_oem_mlx_pkt {
    unsigned char cmd_rev; /* Command Revision  */
    unsigned char cmd; /* Command ID        */
    unsigned char param; /* Parameter         */
    unsigned char optional; /* Optional data     */
    unsigned char data[]; /* Data              */
} SLIRP_PACKED_END;

/* Get Link Status */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gls_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header   */
    __be32 status; /* Link status       */
    __be32 other; /* Other indications */
    __be32 oem_status; /* OEM link status   */
    __be32 checksum;
    unsigned char pad[10];
} SLIRP_PACKED_END;

/* Get Version ID */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gvi_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header */
    __be32 ncsi_version; /* NCSI version    */
    unsigned char reserved[3]; /* Reserved        */
    unsigned char alpha2; /* NCSI version    */
    unsigned char fw_name[12]; /* f/w name string */
    __be32 fw_version; /* f/w version     */
    __be16 pci_ids[4]; /* PCI IDs         */
    __be32 mf_id; /* Manufacture ID  */
    __be32 checksum;
} SLIRP_PACKED_END;

/* Get Capabilities */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gc_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header   */
    __be32 cap; /* Capabilities      */
    __be32 bc_cap; /* Broadcast cap     */
    __be32 mc_cap; /* Multicast cap     */
    __be32 buf_cap; /* Buffering cap     */
    __be32 aen_cap; /* AEN cap           */
    unsigned char vlan_cnt; /* VLAN filter count */
    unsigned char mixed_cnt; /* Mix filter count  */
    unsigned char mc_cnt; /* MC filter count   */
    unsigned char uc_cnt; /* UC filter count   */
    unsigned char reserved[2]; /* Reserved          */
    unsigned char vlan_mode; /* VLAN mode         */
    unsigned char channel_cnt; /* Channel count     */
    __be32 checksum; /* Checksum          */
} SLIRP_PACKED_END;

/* Get Parameters */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gp_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header       */
    unsigned char mac_cnt; /* Number of MAC addr    */
    unsigned char reserved[2]; /* Reserved              */
    unsigned char mac_enable; /* MAC addr enable flags */
    unsigned char vlan_cnt; /* VLAN tag count        */
    unsigned char reserved1; /* Reserved              */
    __be16 vlan_enable; /* VLAN tag enable flags */
    __be32 link_mode; /* Link setting          */
    __be32 bc_mode; /* BC filter mode        */
    __be32 valid_modes; /* Valid mode parameters */
    unsigned char vlan_mode; /* VLAN mode             */
    unsigned char fc_mode; /* Flow control mode     */
    unsigned char reserved2[2]; /* Reserved              */
    __be32 aen_mode; /* AEN mode              */
    unsigned char mac[6]; /* Supported MAC addr    */
    __be16 vlan; /* Supported VLAN tags   */
    __be32 checksum; /* Checksum              */
} SLIRP_PACKED_END;

/* Get Controller Packet Statistics */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gcps_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header            */
    __be32 cnt_hi; /* Counter cleared            */
    __be32 cnt_lo; /* Counter cleared            */
    __be32 rx_bytes; /* Rx bytes                   */
    __be32 tx_bytes; /* Tx bytes                   */
    __be32 rx_uc_pkts; /* Rx UC packets              */
    __be32 rx_mc_pkts; /* Rx MC packets              */
    __be32 rx_bc_pkts; /* Rx BC packets              */
    __be32 tx_uc_pkts; /* Tx UC packets              */
    __be32 tx_mc_pkts; /* Tx MC packets              */
    __be32 tx_bc_pkts; /* Tx BC packets              */
    __be32 fcs_err; /* FCS errors                 */
    __be32 align_err; /* Alignment errors           */
    __be32 false_carrier; /* False carrier detection    */
    __be32 runt_pkts; /* Rx runt packets            */
    __be32 jabber_pkts; /* Rx jabber packets          */
    __be32 rx_pause_xon; /* Rx pause XON frames        */
    __be32 rx_pause_xoff; /* Rx XOFF frames             */
    __be32 tx_pause_xon; /* Tx XON frames              */
    __be32 tx_pause_xoff; /* Tx XOFF frames             */
    __be32 tx_s_collision; /* Single collision frames    */
    __be32 tx_m_collision; /* Multiple collision frames  */
    __be32 l_collision; /* Late collision frames      */
    __be32 e_collision; /* Excessive collision frames */
    __be32 rx_ctl_frames; /* Rx control frames          */
    __be32 rx_64_frames; /* Rx 64-bytes frames         */
    __be32 rx_127_frames; /* Rx 65-127 bytes frames     */
    __be32 rx_255_frames; /* Rx 128-255 bytes frames    */
    __be32 rx_511_frames; /* Rx 256-511 bytes frames    */
    __be32 rx_1023_frames; /* Rx 512-1023 bytes frames   */
    __be32 rx_1522_frames; /* Rx 1024-1522 bytes frames  */
    __be32 rx_9022_frames; /* Rx 1523-9022 bytes frames  */
    __be32 tx_64_frames; /* Tx 64-bytes frames         */
    __be32 tx_127_frames; /* Tx 65-127 bytes frames     */
    __be32 tx_255_frames; /* Tx 128-255 bytes frames    */
    __be32 tx_511_frames; /* Tx 256-511 bytes frames    */
    __be32 tx_1023_frames; /* Tx 512-1023 bytes frames   */
    __be32 tx_1522_frames; /* Tx 1024-1522 bytes frames  */
    __be32 tx_9022_frames; /* Tx 1523-9022 bytes frames  */
    __be32 rx_valid_bytes; /* Rx valid bytes             */
    __be32 rx_runt_pkts; /* Rx error runt packets      */
    __be32 rx_jabber_pkts; /* Rx error jabber packets    */
    __be32 checksum; /* Checksum                   */
} SLIRP_PACKED_END;

/* Get NCSI Statistics */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gns_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header         */
    __be32 rx_cmds; /* Rx NCSI commands        */
    __be32 dropped_cmds; /* Dropped commands        */
    __be32 cmd_type_errs; /* Command type errors     */
    __be32 cmd_csum_errs; /* Command checksum errors */
    __be32 rx_pkts; /* Rx NCSI packets         */
    __be32 tx_pkts; /* Tx NCSI packets         */
    __be32 tx_aen_pkts; /* Tx AEN packets          */
    __be32 checksum; /* Checksum                */
} SLIRP_PACKED_END;

/* Get NCSI Pass-through Statistics */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gnpts_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header     */
    __be32 tx_pkts; /* Tx packets          */
    __be32 tx_dropped; /* Tx dropped packets  */
    __be32 tx_channel_err; /* Tx channel errors   */
    __be32 tx_us_err; /* Tx undersize errors */
    __be32 rx_pkts; /* Rx packets          */
    __be32 rx_dropped; /* Rx dropped packets  */
    __be32 rx_channel_err; /* Rx channel errors   */
    __be32 rx_us_err; /* Rx undersize errors */
    __be32 rx_os_err; /* Rx oversize errors  */
    __be32 checksum; /* Checksum            */
} SLIRP_PACKED_END;

/* Get package status */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gps_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header             */
    __be32 status; /* Hardware arbitration status */
    __be32 checksum;
} SLIRP_PACKED_END;

/* Get package UUID */
SLIRP_PACKED_BEGIN
struct ncsi_rsp_gpuuid_pkt {
    struct ncsi_rsp_pkt_hdr rsp; /* Response header */
    unsigned char uuid[16]; /* UUID            */
    __be32 checksum;
} SLIRP_PACKED_END;

/* AEN: Link State Change */
SLIRP_PACKED_BEGIN
struct ncsi_aen_lsc_pkt {
    struct ncsi_aen_pkt_hdr aen; /* AEN header      */
    __be32 status; /* Link status     */
    __be32 oem_status; /* OEM link status */
    __be32 checksum; /* Checksum        */
    unsigned char pad[14];
} SLIRP_PACKED_END;

/* AEN: Configuration Required */
SLIRP_PACKED_BEGIN
struct ncsi_aen_cr_pkt {
    struct ncsi_aen_pkt_hdr aen; /* AEN header */
    __be32 checksum; /* Checksum   */
    unsigned char pad[22];
} SLIRP_PACKED_END;

/* AEN: Host Network Controller Driver Status Change */
SLIRP_PACKED_BEGIN
struct ncsi_aen_hncdsc_pkt {
    struct ncsi_aen_pkt_hdr aen; /* AEN header */
    __be32 status; /* Status     */
    __be32 checksum; /* Checksum   */
    unsigned char pad[18];
} SLIRP_PACKED_END;

/* NCSI packet revision */
#define NCSI_PKT_REVISION 0x01

/* NCSI packet commands */
#define NCSI_PKT_CMD_CIS 0x00 /* Clear Initial State              */
#define NCSI_PKT_CMD_SP 0x01 /* Select Package                   */
#define NCSI_PKT_CMD_DP 0x02 /* Deselect Package                 */
#define NCSI_PKT_CMD_EC 0x03 /* Enable Channel                   */
#define NCSI_PKT_CMD_DC 0x04 /* Disable Channel                  */
#define NCSI_PKT_CMD_RC 0x05 /* Reset Channel                    */
#define NCSI_PKT_CMD_ECNT 0x06 /* Enable Channel Network Tx        */
#define NCSI_PKT_CMD_DCNT 0x07 /* Disable Channel Network Tx       */
#define NCSI_PKT_CMD_AE 0x08 /* AEN Enable                       */
#define NCSI_PKT_CMD_SL 0x09 /* Set Link                         */
#define NCSI_PKT_CMD_GLS 0x0a /* Get Link                         */
#define NCSI_PKT_CMD_SVF 0x0b /* Set VLAN Filter                  */
#define NCSI_PKT_CMD_EV 0x0c /* Enable VLAN                      */
#define NCSI_PKT_CMD_DV 0x0d /* Disable VLAN                     */
#define NCSI_PKT_CMD_SMA 0x0e /* Set MAC address                  */
#define NCSI_PKT_CMD_EBF 0x10 /* Enable Broadcast Filter          */
#define NCSI_PKT_CMD_DBF 0x11 /* Disable Broadcast Filter         */
#define NCSI_PKT_CMD_EGMF 0x12 /* Enable Global Multicast Filter   */
#define NCSI_PKT_CMD_DGMF 0x13 /* Disable Global Multicast Filter  */
#define NCSI_PKT_CMD_SNFC 0x14 /* Set NCSI Flow Control            */
#define NCSI_PKT_CMD_GVI 0x15 /* Get Version ID                   */
#define NCSI_PKT_CMD_GC 0x16 /* Get Capabilities                 */
#define NCSI_PKT_CMD_GP 0x17 /* Get Parameters                   */
#define NCSI_PKT_CMD_GCPS 0x18 /* Get Controller Packet Statistics */
#define NCSI_PKT_CMD_GNS 0x19 /* Get NCSI Statistics              */
#define NCSI_PKT_CMD_GNPTS 0x1a /* Get NCSI Pass-throu Statistics   */
#define NCSI_PKT_CMD_GPS 0x1b /* Get package status               */
#define NCSI_PKT_CMD_OEM 0x50 /* OEM                              */
#define NCSI_PKT_CMD_PLDM 0x51 /* PLDM request over NCSI over RBT  */
#define NCSI_PKT_CMD_GPUUID 0x52 /* Get package UUID                 */

/* NCSI packet responses */
#define NCSI_PKT_RSP_CIS (NCSI_PKT_CMD_CIS + 0x80)
#define NCSI_PKT_RSP_SP (NCSI_PKT_CMD_SP + 0x80)
#define NCSI_PKT_RSP_DP (NCSI_PKT_CMD_DP + 0x80)
#define NCSI_PKT_RSP_EC (NCSI_PKT_CMD_EC + 0x80)
#define NCSI_PKT_RSP_DC (NCSI_PKT_CMD_DC + 0x80)
#define NCSI_PKT_RSP_RC (NCSI_PKT_CMD_RC + 0x80)
#define NCSI_PKT_RSP_ECNT (NCSI_PKT_CMD_ECNT + 0x80)
#define NCSI_PKT_RSP_DCNT (NCSI_PKT_CMD_DCNT + 0x80)
#define NCSI_PKT_RSP_AE (NCSI_PKT_CMD_AE + 0x80)
#define NCSI_PKT_RSP_SL (NCSI_PKT_CMD_SL + 0x80)
#define NCSI_PKT_RSP_GLS (NCSI_PKT_CMD_GLS + 0x80)
#define NCSI_PKT_RSP_SVF (NCSI_PKT_CMD_SVF + 0x80)
#define NCSI_PKT_RSP_EV (NCSI_PKT_CMD_EV + 0x80)
#define NCSI_PKT_RSP_DV (NCSI_PKT_CMD_DV + 0x80)
#define NCSI_PKT_RSP_SMA (NCSI_PKT_CMD_SMA + 0x80)
#define NCSI_PKT_RSP_EBF (NCSI_PKT_CMD_EBF + 0x80)
#define NCSI_PKT_RSP_DBF (NCSI_PKT_CMD_DBF + 0x80)
#define NCSI_PKT_RSP_EGMF (NCSI_PKT_CMD_EGMF + 0x80)
#define NCSI_PKT_RSP_DGMF (NCSI_PKT_CMD_DGMF + 0x80)
#define NCSI_PKT_RSP_SNFC (NCSI_PKT_CMD_SNFC + 0x80)
#define NCSI_PKT_RSP_GVI (NCSI_PKT_CMD_GVI + 0x80)
#define NCSI_PKT_RSP_GC (NCSI_PKT_CMD_GC + 0x80)
#define NCSI_PKT_RSP_GP (NCSI_PKT_CMD_GP + 0x80)
#define NCSI_PKT_RSP_GCPS (NCSI_PKT_CMD_GCPS + 0x80)
#define NCSI_PKT_RSP_GNS (NCSI_PKT_CMD_GNS + 0x80)
#define NCSI_PKT_RSP_GNPTS (NCSI_PKT_CMD_GNPTS + 0x80)
#define NCSI_PKT_RSP_GPS (NCSI_PKT_CMD_GPS + 0x80)
#define NCSI_PKT_RSP_OEM (NCSI_PKT_CMD_OEM + 0x80)
#define NCSI_PKT_RSP_PLDM (NCSI_PKT_CMD_PLDM + 0x80)
#define NCSI_PKT_RSP_GPUUID (NCSI_PKT_CMD_GPUUID + 0x80)

/* NCSI response code/reason */
#define NCSI_PKT_RSP_C_COMPLETED 0x0000 /* Command Completed        */
#define NCSI_PKT_RSP_C_FAILED 0x0001 /* Command Failed           */
#define NCSI_PKT_RSP_C_UNAVAILABLE 0x0002 /* Command Unavailable      */
#define NCSI_PKT_RSP_C_UNSUPPORTED 0x0003 /* Command Unsupported      */
#define NCSI_PKT_RSP_R_NO_ERROR 0x0000 /* No Error                 */
#define NCSI_PKT_RSP_R_INTERFACE 0x0001 /* Interface not ready      */
#define NCSI_PKT_RSP_R_PARAM 0x0002 /* Invalid Parameter        */
#define NCSI_PKT_RSP_R_CHANNEL 0x0003 /* Channel not Ready        */
#define NCSI_PKT_RSP_R_PACKAGE 0x0004 /* Package not Ready        */
#define NCSI_PKT_RSP_R_LENGTH 0x0005 /* Invalid payload length   */
#define NCSI_PKT_RSP_R_UNKNOWN 0x7fff /* Command type unsupported */

/* NCSI AEN packet type */
#define NCSI_PKT_AEN 0xFF /* AEN Packet               */
#define NCSI_PKT_AEN_LSC 0x00 /* Link status change       */
#define NCSI_PKT_AEN_CR 0x01 /* Configuration required   */
#define NCSI_PKT_AEN_HNCDSC 0x02 /* HNC driver status change */

/* OEM Vendor Manufacture ID */
#define NCSI_OEM_MFR_MLX_ID 0x8119
#define NCSI_OEM_MFR_BCM_ID 0x113d
#define NCSI_OEM_MFR_INTEL_ID 0x157
/* Intel specific OEM command */
#define NCSI_OEM_INTEL_CMD_GMA 0x06 /* CMD ID for Get MAC */
#define NCSI_OEM_INTEL_CMD_KEEP_PHY 0x20 /* CMD ID for Keep PHY up */
/* Broadcom specific OEM Command */
#define NCSI_OEM_BCM_CMD_GMA 0x01 /* CMD ID for Get MAC */
/* Mellanox specific OEM Command */
#define NCSI_OEM_MLX_CMD_GMA 0x00 /* CMD ID for Get MAC */
#define NCSI_OEM_MLX_CMD_GMA_PARAM 0x1b /* Parameter for GMA */
#define NCSI_OEM_MLX_CMD_SMAF 0x01 /* CMD ID for Set MC Affinity */
#define NCSI_OEM_MLX_CMD_SMAF_PARAM 0x07 /* Parameter for SMAF */
/* Offset in OEM request */
#define MLX_SMAF_MAC_ADDR_OFFSET 8 /* Offset for MAC in SMAF */
#define MLX_SMAF_MED_SUPPORT_OFFSET 14 /* Offset for medium in SMAF */
/* Mac address offset in OEM response */
#define BCM_MAC_ADDR_OFFSET 28
#define MLX_MAC_ADDR_OFFSET 8
#define INTEL_MAC_ADDR_OFFSET 1

/* Status offset in OEM response */
#define MLX_GMA_STATUS_OFFSET 0
/* OEM Response payload length */
#define MLX_GMA_PAYLOAD_LEN 24

#endif /* NCSI_PKT_H */
