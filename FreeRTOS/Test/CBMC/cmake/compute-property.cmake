execute_process(
    COMMAND
        cbmc --show-properties --unwinding-assertions --xml-ui
        ${cbmc_flags} ${cbmc_verbosity} ${goto_binary}
    OUTPUT_FILE ${out_file}
    ERROR_FILE ${out_file}
    RESULT_VARIABLE res
)

if(NOT (${res} EQUAL 0 OR ${res} EQUAL 10))
    message(FATAL_ERROR
        "Unexpected CBMC property return code '${res}' for proof ${proof_name}. Log written to ${out_file}."
    )
endif()
