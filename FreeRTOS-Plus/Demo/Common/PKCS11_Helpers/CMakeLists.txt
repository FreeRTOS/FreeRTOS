# Module for corePKCS11 library based helper utilities. 
afr_module(NAME pkcs11_helpers)

afr_module_sources(
    ${AFR_CURRENT_MODULE}
    PRIVATE
        ${CMAKE_CURRENT_LIST_DIR}/pkcs11_helpers.c
)

afr_module_include_dirs(
    ${AFR_CURRENT_MODULE}
    PUBLIC
       "${CMAKE_CURRENT_LIST_DIR}"
)

afr_module_dependencies(
    ${AFR_CURRENT_MODULE}
    PUBLIC
        AFR::pkcs11_implementation
    PRIVATE
        AFR::logging
)
