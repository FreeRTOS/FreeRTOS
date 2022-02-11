/*
 * Percepio Trace Recorder Initialization v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * This file should only be included in a project if there is a need to
 * initialize the Trace Recorder before main() has been called.
 * An example of this scenario is if you have a global object instance that has
 * a constructor that creates an object that should be traced.
 * This file will make it easier to initiate the recorder correctly.
 *
 * Usage:
 *	Add a call to TraceRecorderInit::Initialize() wherever a traced object is
 *	created before the Trace Recorder is normally initialized. This will ensure
 *	the Trace Recorder is initialized only once.
 *
 *	Set TRC_CFG_RECORDER_DATA_PTR_INIT to 0 in trcSnapshotConfig.h to ensure
 *	RecorderInitialized isn't initialized to 0 after the recorder has been
 *	already initialized.
 *
 *	Finally, call vTraceEnable(TRC_START) after hardware is initialized to
 *	start gathering trace events.
 */
 
#include <TraceRecorderInit.h>
#include <trcRecorder.h>

extern "C" uint32_t RecorderInitialized;

/* Public */
bool TraceRecorderInit::Initialize()
{
	/* Lazy initialization, and constructor is only run once ensuring that we only initialize the recorder once */
	static TraceRecorderInit instance;

	return instance.IsInitialized();
}

/* Private */
TraceRecorderInit::TraceRecorderInit()
{
	RecorderInitialized = 0;
	xTraceInitialize();
}

TraceRecorderInit::~TraceRecorderInit()
{
}

bool TraceRecorderInit::IsInitialized()
{
	return RecorderInitialized != 0;
}
