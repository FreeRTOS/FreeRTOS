This proof demonstrates ubounded memory safety of the TaskCreateRestricted 
and TaskCreateRestrictedStatic functions.

The compilation may complain about a duplicate definition of 
the MPU_WRAPPERS_INCLUDED_FROM_API_FILE constant, but it is necessary
to ensure that the TaskCreateRestricted functions we care about get compiled.