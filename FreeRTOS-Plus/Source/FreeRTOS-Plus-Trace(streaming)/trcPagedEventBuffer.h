/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcPagedEventBuffer.h
 *
 * Implements a paged buffer that can be used by TCP/IP or custom transfer
 * methods.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
 *
 * Disclaimer
 * The trace tool and recorder library is being delivered to you AS IS and
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does
 * not and cannot warrant the performance or results you may obtain by using the
 * software or documentation. Percepio AB make no warranties, express or
 * implied, as to noninfringement of third party rights, merchantability, or
 * fitness for any particular purpose. In no event will Percepio AB, its
 * technology partners, or distributors be liable to you for any consequential,
 * incidental or special damages, including any lost profits or lost savings,
 * even if a representative of Percepio AB has been advised of the possibility
 * of such damages, or for any claim by any third party. Some jurisdictions do
 * not allow the exclusion or limitation of incidental, consequential or special
 * damages, or the exclusion of implied warranties or limitations on how long an
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_PAGED_EVENT_BUFFER_H
#define TRC_PAGED_EVENT_BUFFER_H

#ifdef __cplusplus
extern “C” {
#endif

void vPagedEventBufferInit(char* buffer);

void* vPagedEventBufferGetWritePointer(int sizeOfEvent);

int32_t vPagedEventBufferTransfer(int32_t (*writeFunc)(void* data, uint32_t size, int32_t* ptrBytesWritten), int32_t* nofBytes);

void vPagedEventBufferReset(void);

#ifdef __cplusplus
}
#endif

#endif /*TRC_PAGED_EVENT_BUFFER_H*/