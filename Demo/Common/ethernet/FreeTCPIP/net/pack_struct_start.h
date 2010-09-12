#ifdef __GNUC__

/* Nothing to do here. */
;
#endif

/* Used by SH2A port. */
#ifdef _SH
	#ifdef __RENESAS__
		#pragma pack 1
	#endif
#endif


#ifdef __RX
	#ifdef __RENESAS__
		/* Nothing to do. */
	#endif
#endif


#ifdef __ICCRX__
	#pragma pack(1)
#endif
