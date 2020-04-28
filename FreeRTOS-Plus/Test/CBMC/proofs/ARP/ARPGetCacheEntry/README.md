The combined proofs in the subdirectories prove that ARPGetCacheEntry
is memory safe for all possible combinations of ipconfigARP_STORES_REMOTE_ADDRESSES
and ipconfigUSE_LLMNR. These are the only configuration
parameters used inside the ARPGetCacheEntry.
