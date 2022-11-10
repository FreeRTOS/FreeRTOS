Percepio Trace Recorder Initialization v4.6.0
Copyright 2021 Percepio AB
www.percepio.com

This folder contains files that should only be included in a project
if there is a need to initialize the Trace Recorder before main()
has been called.

An example of this scenario is if you have a global object instance that has
a constructor that creates an object that should be traced.
TraceRecorderInit will make it easier to initiate the recorder correctly.

Usage:
Add a call to TraceRecorderInit::Initialize() wherever a traced object
is created before the Trace Recorder is normally initialized, or simply
as early as absloutely possible. This will ensure the Trace Recorder is
initialized only once.

Set TRC_CFG_RECORDER_DATA_INIT to 0 in trcConfig.h to ensure
recorder data isn't initialized cleared after the recorder has been
already initialized.

It is possible that you also need to make sure certain recorder data isn't
cleared when RAM sections are initialized. Create a RAM section that isn't
cleared, then set the appropriate attribute in TRC_CFG_RECORDER_DATA_ATTRIBUTE.
This attribute will then be set for all necessary recorder data that should
not be cleared.

After the hardware and clocks are properly initialized, use
vTraceEnable(TRC_START) to start the tracing.
