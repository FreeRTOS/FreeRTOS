/*****************************************************************************
* fsm.c - Network Control Protocol Finite State Machine program file.
*
* Copyright (c) 2003 by Marc Boucher, Services Informatiques (MBSI) inc.
* portions Copyright (c) 1997 by Global Election Systems Inc.
*
* The authors hereby grant permission to use, copy, modify, distribute,
* and license this software and its documentation for any purpose, provided
* that existing copyright notices are retained in all copies and that this
* notice and the following disclaimer are included verbatim in any 
* distributions. No written agreement, license, or royalty fee is required
* for any of the authorized uses.
*
* THIS SOFTWARE IS PROVIDED BY THE CONTRIBUTORS *AS IS* AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
* OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
* IN NO EVENT SHALL THE CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
* NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
* THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*
******************************************************************************
* REVISION HISTORY
*
* 03-01-01 Marc Boucher <marc@mbsi.ca>
*   Ported to lwIP.
* 97-12-01 Guy Lancaster <lancasterg@acm.org>, Global Election Systems Inc.
*	Original based on BSD fsm.c.
*****************************************************************************/
/*
 * fsm.c - {Link, IP} Control Protocol Finite State Machine.
 *
 * Copyright (c) 1989 Carnegie Mellon University.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * advertising materials, and other materials related to such
 * distribution and use acknowledge that the software was developed
 * by Carnegie Mellon University.  The name of the
 * University may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 */


/*
 * TODO:
 * Randomize fsm id on link/init.
 * Deal with variable outgoing MTU.
 */

#include "ppp.h"
#if PPP_SUPPORT > 0
#include "fsm.h"
#include "pppdebug.h"


/*************************/
/*** LOCAL DEFINITIONS ***/
/*************************/


/************************/
/*** LOCAL DATA TYPES ***/
/************************/


/***********************************/
/*** LOCAL FUNCTION DECLARATIONS ***/
/***********************************/
static void fsm_timeout (void *);
static void fsm_rconfreq (fsm *, u_char, u_char *, int);
static void fsm_rconfack (fsm *, int, u_char *, int);
static void fsm_rconfnakrej (fsm *, int, int, u_char *, int);
static void fsm_rtermreq (fsm *, int, u_char *, int);
static void fsm_rtermack (fsm *);
static void fsm_rcoderej (fsm *, u_char *, int);
static void fsm_sconfreq (fsm *, int);

#define PROTO_NAME(f)	((f)->callbacks->proto_name)


/******************************/
/*** PUBLIC DATA STRUCTURES ***/
/******************************/


/*****************************/
/*** LOCAL DATA STRUCTURES ***/
/*****************************/
int peer_mru[NUM_PPP];


/***********************************/
/*** PUBLIC FUNCTION DEFINITIONS ***/
/***********************************/

/*
 * fsm_init - Initialize fsm.
 *
 * Initialize fsm state.
 */
void fsm_init(fsm *f)
{
	f->state = INITIAL;
	f->flags = 0;
	f->id = 0;				/* XXX Start with random id? */
	f->timeouttime = FSM_DEFTIMEOUT;
	f->maxconfreqtransmits = FSM_DEFMAXCONFREQS;
	f->maxtermtransmits = FSM_DEFMAXTERMREQS;
	f->maxnakloops = FSM_DEFMAXNAKLOOPS;
	f->term_reason_len = 0;
}


/*
 * fsm_lowerup - The lower layer is up.
 */
void fsm_lowerup(fsm *f)
{
	int oldState = f->state;

	switch( f->state ){
	case INITIAL:
		f->state = CLOSED;
		break;
	
	case STARTING:
		if( f->flags & OPT_SILENT )
			f->state = STOPPED;
		else {
			/* Send an initial configure-request */
			fsm_sconfreq(f, 0);
			f->state = REQSENT;
		}
	break;
	
	default:
		FSMDEBUG((LOG_INFO, "%s: Up event in state %d!\n",
				PROTO_NAME(f), f->state));
	}
	
	FSMDEBUG((LOG_INFO, "%s: lowerup state %d -> %d\n",
			PROTO_NAME(f), oldState, f->state));
}


/*
 * fsm_lowerdown - The lower layer is down.
 *
 * Cancel all timeouts and inform upper layers.
 */
void fsm_lowerdown(fsm *f)
{
	int oldState = f->state;
	
	switch( f->state ){
	case CLOSED:
		f->state = INITIAL;
		break;
	
	case STOPPED:
		f->state = STARTING;
		if( f->callbacks->starting )
			(*f->callbacks->starting)(f);
		break;
	
	case CLOSING:
		f->state = INITIAL;
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		break;
	
	case STOPPING:
	case REQSENT:
	case ACKRCVD:
	case ACKSENT:
		f->state = STARTING;
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		break;
	
	case OPENED:
		if( f->callbacks->down )
			(*f->callbacks->down)(f);
		f->state = STARTING;
		break;
	
	default:
		FSMDEBUG((LOG_INFO, "%s: Down event in state %d!\n",
				PROTO_NAME(f), f->state));
	}
	
	FSMDEBUG((LOG_INFO, "%s: lowerdown state %d -> %d\n",
			PROTO_NAME(f), oldState, f->state));
}


/*
 * fsm_open - Link is allowed to come up.
 */
void fsm_open(fsm *f)
{
	int oldState = f->state;
	
	switch( f->state ){
		case INITIAL:
			f->state = STARTING;
			if( f->callbacks->starting )
				(*f->callbacks->starting)(f);
			break;
		
		case CLOSED:
		if( f->flags & OPT_SILENT )
			f->state = STOPPED;
		else {
			/* Send an initial configure-request */
			fsm_sconfreq(f, 0);
			f->state = REQSENT;
		}
		break;
	
	case CLOSING:
		f->state = STOPPING;
		/* fall through */
	case STOPPED:
	case OPENED:
		if( f->flags & OPT_RESTART ){
			fsm_lowerdown(f);
			fsm_lowerup(f);
		}
		break;
	}
	
	FSMDEBUG((LOG_INFO, "%s: open state %d -> %d\n",
			PROTO_NAME(f), oldState, f->state));
}


/*
 * fsm_close - Start closing connection.
 *
 * Cancel timeouts and either initiate close or possibly go directly to
 * the CLOSED state.
 */
void fsm_close(fsm *f, char *reason)
{
	int oldState = f->state;
	
	f->term_reason = reason;
	f->term_reason_len = (reason == NULL? 0: strlen(reason));
	switch( f->state ){
	case STARTING:
		f->state = INITIAL;
		break;
	case STOPPED:
		f->state = CLOSED;
		break;
	case STOPPING:
		f->state = CLOSING;
		break;
	
	case REQSENT:
	case ACKRCVD:
	case ACKSENT:
	case OPENED:
		if( f->state != OPENED )
			UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		else if( f->callbacks->down )
			(*f->callbacks->down)(f);	/* Inform upper layers we're down */
		
		/* Init restart counter, send Terminate-Request */
		f->retransmits = f->maxtermtransmits;
		fsm_sdata(f, TERMREQ, f->reqid = ++f->id,
					(u_char *) f->term_reason, f->term_reason_len);
		TIMEOUT(fsm_timeout, f, f->timeouttime);
		--f->retransmits;
		
		f->state = CLOSING;
		break;
	}
	
	FSMDEBUG((LOG_INFO, "%s: close reason=%s state %d -> %d\n",
			PROTO_NAME(f), reason, oldState, f->state));
}


/*
 * fsm_sdata - Send some data.
 *
 * Used for all packets sent to our peer by this module.
 */
void fsm_sdata(
	fsm *f,
	u_char code, 
	u_char id,
	u_char *data,
	int datalen
)
{
	u_char *outp;
	int outlen;
	
	/* Adjust length to be smaller than MTU */
	outp = outpacket_buf[f->unit];
	if (datalen > peer_mru[f->unit] - (int)HEADERLEN)
		datalen = peer_mru[f->unit] - HEADERLEN;
	if (datalen && data != outp + PPP_HDRLEN + HEADERLEN)
		BCOPY(data, outp + PPP_HDRLEN + HEADERLEN, datalen);
	outlen = datalen + HEADERLEN;
	MAKEHEADER(outp, f->protocol);
	PUTCHAR(code, outp);
	PUTCHAR(id, outp);
	PUTSHORT(outlen, outp);
	pppWrite(f->unit, outpacket_buf[f->unit], outlen + PPP_HDRLEN);
	FSMDEBUG((LOG_INFO, "fsm_sdata(%s): Sent code %d,%d,%d.\n",
				PROTO_NAME(f), code, id, outlen));
}


/*
 * fsm_input - Input packet.
 */
void fsm_input(fsm *f, u_char *inpacket, int l)
{
	u_char *inp = inpacket;
	u_char code, id;
	int len;
	
	/*
	* Parse header (code, id and length).
	* If packet too short, drop it.
	*/
	if (l < HEADERLEN) {
		FSMDEBUG((LOG_WARNING, "fsm_input(%x): Rcvd short header.\n",
					f->protocol));
		return;
	}
	GETCHAR(code, inp);
	GETCHAR(id, inp);
	GETSHORT(len, inp);
	if (len < HEADERLEN) {
		FSMDEBUG((LOG_INFO, "fsm_input(%x): Rcvd illegal length.\n",
				f->protocol));
		return;
	}
	if (len > l) {
		FSMDEBUG((LOG_INFO, "fsm_input(%x): Rcvd short packet.\n",
				f->protocol));
		return;
	}
	len -= HEADERLEN;		/* subtract header length */
	
	if( f->state == INITIAL || f->state == STARTING ){
		FSMDEBUG((LOG_INFO, "fsm_input(%x): Rcvd packet in state %d.\n",
				f->protocol, f->state));
		return;
	}
	FSMDEBUG((LOG_INFO, "fsm_input(%s):%d,%d,%d\n", PROTO_NAME(f), code, id, l));
	/*
	 * Action depends on code.
	 */
	switch (code) {
	case CONFREQ:
		fsm_rconfreq(f, id, inp, len);
		break;
	
	case CONFACK:
		fsm_rconfack(f, id, inp, len);
		break;
	
	case CONFNAK:
	case CONFREJ:
		fsm_rconfnakrej(f, code, id, inp, len);
		break;
	
	case TERMREQ:
		fsm_rtermreq(f, id, inp, len);
		break;
	
	case TERMACK:
		fsm_rtermack(f);
		break;
	
	case CODEREJ:
		fsm_rcoderej(f, inp, len);
		break;
	
	default:
		if( !f->callbacks->extcode
				|| !(*f->callbacks->extcode)(f, code, id, inp, len) )
			fsm_sdata(f, CODEREJ, ++f->id, inpacket, len + HEADERLEN);
		break;
	}
}


/*
 * fsm_protreject - Peer doesn't speak this protocol.
 *
 * Treat this as a catastrophic error (RXJ-).
 */
void fsm_protreject(fsm *f)
{
	switch( f->state ){
	case CLOSING:
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		/* fall through */
	case CLOSED:
		f->state = CLOSED;
		if( f->callbacks->finished )
			(*f->callbacks->finished)(f);
		break;
	
	case STOPPING:
	case REQSENT:
	case ACKRCVD:
	case ACKSENT:
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		/* fall through */
	case STOPPED:
		f->state = STOPPED;
		if( f->callbacks->finished )
			(*f->callbacks->finished)(f);
		break;
	
	case OPENED:
		if( f->callbacks->down )
			(*f->callbacks->down)(f);
		
		/* Init restart counter, send Terminate-Request */
		f->retransmits = f->maxtermtransmits;
		fsm_sdata(f, TERMREQ, f->reqid = ++f->id,
					(u_char *) f->term_reason, f->term_reason_len);
		TIMEOUT(fsm_timeout, f, f->timeouttime);
		--f->retransmits;
		
		f->state = STOPPING;
		break;
	
	default:
		FSMDEBUG((LOG_INFO, "%s: Protocol-reject event in state %d!\n",
					PROTO_NAME(f), f->state));
	}
}





/**********************************/
/*** LOCAL FUNCTION DEFINITIONS ***/
/**********************************/

/*
 * fsm_timeout - Timeout expired.
 */
static void fsm_timeout(void *arg)
{
    fsm *f = (fsm *) arg;

    switch (f->state) {
    case CLOSING:
    case STOPPING:
		if( f->retransmits <= 0 ){
		    FSMDEBUG((LOG_WARNING, "%s: timeout sending Terminate-Request state=%d\n",
					   PROTO_NAME(f), f->state));
		    /*
		     * We've waited for an ack long enough.  Peer probably heard us.
		     */
		    f->state = (f->state == CLOSING)? CLOSED: STOPPED;
		    if( f->callbacks->finished )
			(*f->callbacks->finished)(f);
		} else {
		    FSMDEBUG((LOG_WARNING, "%s: timeout resending Terminate-Requests state=%d\n",
					   PROTO_NAME(f), f->state));
		    /* Send Terminate-Request */
		    fsm_sdata(f, TERMREQ, f->reqid = ++f->id,
			      (u_char *) f->term_reason, f->term_reason_len);
		    TIMEOUT(fsm_timeout, f, f->timeouttime);
		    --f->retransmits;
		}
		break;

    case REQSENT:
    case ACKRCVD:
    case ACKSENT:
		if (f->retransmits <= 0) {
		    FSMDEBUG((LOG_WARNING, "%s: timeout sending Config-Requests state=%d\n",
			   PROTO_NAME(f), f->state));
		    f->state = STOPPED;
		    if( (f->flags & OPT_PASSIVE) == 0 && f->callbacks->finished )
				(*f->callbacks->finished)(f);
	
		} else {
		    FSMDEBUG((LOG_WARNING, "%s: timeout resending Config-Request state=%d\n",
			   PROTO_NAME(f), f->state));
		    /* Retransmit the configure-request */
		    if (f->callbacks->retransmit)
				(*f->callbacks->retransmit)(f);
		    fsm_sconfreq(f, 1);		/* Re-send Configure-Request */
		    if( f->state == ACKRCVD )
				f->state = REQSENT;
		}
		break;

    default:
		FSMDEBUG((LOG_INFO, "%s: Timeout event in state %d!\n",
				  PROTO_NAME(f), f->state));
	    }
}


/*
 * fsm_rconfreq - Receive Configure-Request.
 */
static void fsm_rconfreq(fsm *f, u_char id, u_char *inp, int len)
{
	int code, reject_if_disagree;
	
	FSMDEBUG((LOG_INFO, "fsm_rconfreq(%s): Rcvd id %d state=%d\n", 
				PROTO_NAME(f), id, f->state));
	switch( f->state ){
	case CLOSED:
		/* Go away, we're closed */
		fsm_sdata(f, TERMACK, id, NULL, 0);
		return;
	case CLOSING:
	case STOPPING:
		return;
	
	case OPENED:
		/* Go down and restart negotiation */
		if( f->callbacks->down )
			(*f->callbacks->down)(f);	/* Inform upper layers */
		fsm_sconfreq(f, 0);		/* Send initial Configure-Request */
		break;
	
	case STOPPED:
		/* Negotiation started by our peer */
		fsm_sconfreq(f, 0);		/* Send initial Configure-Request */
		f->state = REQSENT;
		break;
	}
	
	/*
	* Pass the requested configuration options
	* to protocol-specific code for checking.
	*/
	if (f->callbacks->reqci){		/* Check CI */
		reject_if_disagree = (f->nakloops >= f->maxnakloops);
		code = (*f->callbacks->reqci)(f, inp, &len, reject_if_disagree);
	} 
	else if (len)
		code = CONFREJ;			/* Reject all CI */
	else
		code = CONFACK;
	
	/* send the Ack, Nak or Rej to the peer */
	fsm_sdata(f, (u_char)code, id, inp, len);
	
	if (code == CONFACK) {
		if (f->state == ACKRCVD) {
			UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
			f->state = OPENED;
			if (f->callbacks->up)
				(*f->callbacks->up)(f);	/* Inform upper layers */
		} 
		else
			f->state = ACKSENT;
		f->nakloops = 0;
	} 
	else {
		/* we sent CONFACK or CONFREJ */
		if (f->state != ACKRCVD)
			f->state = REQSENT;
		if( code == CONFNAK )
			++f->nakloops;
	}
}


/*
 * fsm_rconfack - Receive Configure-Ack.
 */
static void fsm_rconfack(fsm *f, int id, u_char *inp, int len)
{
	FSMDEBUG((LOG_INFO, "fsm_rconfack(%s): Rcvd id %d state=%d\n",
				PROTO_NAME(f), id, f->state));
	
	if (id != f->reqid || f->seen_ack)		/* Expected id? */
		return;					/* Nope, toss... */
	if( !(f->callbacks->ackci? (*f->callbacks->ackci)(f, inp, len):
								(len == 0)) ){
		/* Ack is bad - ignore it */
		FSMDEBUG((LOG_INFO, "%s: received bad Ack (length %d)\n",
					PROTO_NAME(f), len));
		return;
	}
	f->seen_ack = 1;
	
	switch (f->state) {
	case CLOSED:
	case STOPPED:
		fsm_sdata(f, TERMACK, (u_char)id, NULL, 0);
		break;
	
	case REQSENT:
		f->state = ACKRCVD;
		f->retransmits = f->maxconfreqtransmits;
		break;
	
	case ACKRCVD:
		/* Huh? an extra valid Ack? oh well... */
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		fsm_sconfreq(f, 0);
		f->state = REQSENT;
		break;
	
	case ACKSENT:
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		f->state = OPENED;
		f->retransmits = f->maxconfreqtransmits;
		if (f->callbacks->up)
			(*f->callbacks->up)(f);	/* Inform upper layers */
		break;
	
	case OPENED:
		/* Go down and restart negotiation */
		if (f->callbacks->down)
			(*f->callbacks->down)(f);	/* Inform upper layers */
		fsm_sconfreq(f, 0);		/* Send initial Configure-Request */
		f->state = REQSENT;
		break;
	}
}


/*
 * fsm_rconfnakrej - Receive Configure-Nak or Configure-Reject.
 */
static void fsm_rconfnakrej(fsm *f, int code, int id, u_char *inp, int len)
{
	int (*proc) (fsm *, u_char *, int);
	int ret;
	
	FSMDEBUG((LOG_INFO, "fsm_rconfnakrej(%s): Rcvd id %d state=%d\n",
				PROTO_NAME(f), id, f->state));
	
	if (id != f->reqid || f->seen_ack)	/* Expected id? */
		return;				/* Nope, toss... */
	proc = (code == CONFNAK)? f->callbacks->nakci: f->callbacks->rejci;
	if (!proc || !(ret = proc(f, inp, len))) {
		/* Nak/reject is bad - ignore it */
		FSMDEBUG((LOG_INFO, "%s: received bad %s (length %d)\n",
					PROTO_NAME(f), (code==CONFNAK? "Nak": "reject"), len));
		return;
	}
	f->seen_ack = 1;
	
	switch (f->state) {
	case CLOSED:
	case STOPPED:
		fsm_sdata(f, TERMACK, (u_char)id, NULL, 0);
		break;
	
	case REQSENT:
	case ACKSENT:
		/* They didn't agree to what we wanted - try another request */
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		if (ret < 0)
			f->state = STOPPED;		/* kludge for stopping CCP */
		else
			fsm_sconfreq(f, 0);		/* Send Configure-Request */
		break;
	
	case ACKRCVD:
		/* Got a Nak/reject when we had already had an Ack?? oh well... */
		UNTIMEOUT(fsm_timeout, f);	/* Cancel timeout */
		fsm_sconfreq(f, 0);
		f->state = REQSENT;
		break;
	
	case OPENED:
		/* Go down and restart negotiation */
		if (f->callbacks->down)
			(*f->callbacks->down)(f);	/* Inform upper layers */
		fsm_sconfreq(f, 0);		/* Send initial Configure-Request */
		f->state = REQSENT;
		break;
	}
}


/*
 * fsm_rtermreq - Receive Terminate-Req.
 */
static void fsm_rtermreq(fsm *f, int id, u_char *p, int len)
{
	FSMDEBUG((LOG_INFO, "fsm_rtermreq(%s): Rcvd id %d state=%d\n",
				PROTO_NAME(f), id, f->state));
	
	switch (f->state) {
	case ACKRCVD:
	case ACKSENT:
		f->state = REQSENT;		/* Start over but keep trying */
		break;
	
	case OPENED:
		if (len > 0) {
			FSMDEBUG((LOG_INFO, "%s terminated by peer (%x)\n", PROTO_NAME(f), p));
		} else {
			FSMDEBUG((LOG_INFO, "%s terminated by peer\n", PROTO_NAME(f)));
		}
		if (f->callbacks->down)
			(*f->callbacks->down)(f);	/* Inform upper layers */
		f->retransmits = 0;
		f->state = STOPPING;
		TIMEOUT(fsm_timeout, f, f->timeouttime);
		break;
	}
	
	fsm_sdata(f, TERMACK, (u_char)id, NULL, 0);
}


/*
 * fsm_rtermack - Receive Terminate-Ack.
 */
static void fsm_rtermack(fsm *f)
{
	FSMDEBUG((LOG_INFO, "fsm_rtermack(%s): state=%d\n", 
				PROTO_NAME(f), f->state));
	
	switch (f->state) {
	case CLOSING:
		UNTIMEOUT(fsm_timeout, f);
		f->state = CLOSED;
		if( f->callbacks->finished )
			(*f->callbacks->finished)(f);
		break;
	case STOPPING:
		UNTIMEOUT(fsm_timeout, f);
		f->state = STOPPED;
		if( f->callbacks->finished )
			(*f->callbacks->finished)(f);
		break;
	
	case ACKRCVD:
		f->state = REQSENT;
		break;
	
	case OPENED:
		if (f->callbacks->down)
			(*f->callbacks->down)(f);	/* Inform upper layers */
		fsm_sconfreq(f, 0);
		break;
	}
}


/*
 * fsm_rcoderej - Receive an Code-Reject.
 */
static void fsm_rcoderej(fsm *f, u_char *inp, int len)
{
	u_char code, id;
	
	FSMDEBUG((LOG_INFO, "fsm_rcoderej(%s): state=%d\n", 
				PROTO_NAME(f), f->state));
	
	if (len < HEADERLEN) {
		FSMDEBUG((LOG_INFO, "fsm_rcoderej: Rcvd short Code-Reject packet!\n"));
		return;
	}
	GETCHAR(code, inp);
	GETCHAR(id, inp);
	FSMDEBUG((LOG_WARNING, "%s: Rcvd Code-Reject for code %d, id %d\n",
				PROTO_NAME(f), code, id));
	
	if( f->state == ACKRCVD )
		f->state = REQSENT;
}


/*
 * fsm_sconfreq - Send a Configure-Request.
 */
static void fsm_sconfreq(fsm *f, int retransmit)
{
	u_char *outp;
	int cilen;
	
	if( f->state != REQSENT && f->state != ACKRCVD && f->state != ACKSENT ){
		/* Not currently negotiating - reset options */
		if( f->callbacks->resetci )
			(*f->callbacks->resetci)(f);
		f->nakloops = 0;
		}
	
	if( !retransmit ){
		/* New request - reset retransmission counter, use new ID */
		f->retransmits = f->maxconfreqtransmits;
		f->reqid = ++f->id;
	}
	
	f->seen_ack = 0;
	
	/*
	 * Make up the request packet
	 */
	outp = outpacket_buf[f->unit] + PPP_HDRLEN + HEADERLEN;
	if( f->callbacks->cilen && f->callbacks->addci ){
		cilen = (*f->callbacks->cilen)(f);
		if( cilen > peer_mru[f->unit] - (int)HEADERLEN )
			cilen = peer_mru[f->unit] - HEADERLEN;
		if (f->callbacks->addci)
			(*f->callbacks->addci)(f, outp, &cilen);
	} else
		cilen = 0;
	
	/* send the request to our peer */
	fsm_sdata(f, CONFREQ, f->reqid, outp, cilen);
	
	/* start the retransmit timer */
	--f->retransmits;
	TIMEOUT(fsm_timeout, f, f->timeouttime);
	
	FSMDEBUG((LOG_INFO, "%s: sending Configure-Request, id %d\n",
				PROTO_NAME(f), f->reqid));
}

#endif /* PPP_SUPPORT */
