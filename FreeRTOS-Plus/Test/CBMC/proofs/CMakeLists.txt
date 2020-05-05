list(APPEND cbmc_compile_options
    -m32
)

list(APPEND cbmc_compile_definitions
    CBMC
    WINVER=0x400
    _CONSOLE
    _CRT_SECURE_NO_WARNINGS
    _DEBUG
    _WIN32_WINNT=0x0500
    __PRETTY_FUNCTION__=__FUNCTION__
    __free_rtos__
)

list(APPEND cbmc_compile_includes
    ${CMAKE_SOURCE_DIR}/Source/include
    ${CMAKE_SOURCE_DIR}/Source/portable/MSVC-MingW
	${CMAKE_SOURCE_DIR}/Source/../../FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP/portable/BufferManagement
	${CMAKE_SOURCE_DIR}/Source/../../FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP/include    
    ${CMAKE_SOURCE_DIR}/Source/../../FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP/portable/Compiler/MSVC
    ${cbmc_dir}/include
    ${cbmc_dir}/windows
)

# Remove --flag for a specific proof with list(REMOVE_ITEM cbmc_flags --flag)
list(APPEND cbmc_flags
    --32
    --bounds-check
    --pointer-check
    --div-by-zero-check
    --float-overflow-check
    --nan-check
    --nondet-static
    --pointer-overflow-check
    --signed-overflow-check
    --undefined-shift-check
    --unsigned-overflow-check
)

