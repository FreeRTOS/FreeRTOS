#ifdef __GNUC__
	__attribute__( (packed) );
#endif

#ifdef _SH
	#ifdef __RENESAS__
		;
		#pragma unpack
	#endif
#endif

#ifdef __RX
	#ifdef __RENESAS__
		;
		/* Nothing to do. */
	#endif
#endif


#ifdef __ICCRX__
	;
	#pragma pack()
#endif
