/*****************************************************************************
* © 2015 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/



#ifndef INCLUDE_CEC1302_CRYPTO_API_H_
#define INCLUDE_CEC1302_CRYPTO_API_H_

#include <stdint.h>
#include <stdbool.h>
#ifdef __cplusplus
extern "C" {
#endif

/* Misc. */

/* RNG */
/**
 *  \rng_power
 *  
 *  \param [in] pwr_on Power On?
 *  \return none
 *  
 *  \details Gate clocks on/off to NDRNG block
 */
extern void
rng_power(bool pwr_on);


/**
 *  \rng_reset
 *  
 *  \return Reset NDRNG block
 *  
 *  \details 
 */
extern void
rng_reset(void);


/**
 *  \rng_mode
 *  
 *  \param [in] mode tmode_pseudo 0(asynchronous/true random mode), 
 *              Non-zero(pseudo-random mode)
 *  \return None
 *  
 *  \details Set NDRNG random number generation mode
 */
extern void
rng_mode(uint8_t mode);


/**
 *  \rng_is_on
 *  
 *  \return is NDRNG Block powered on? True if yes, false otherwise
 *  
 *  \details Check if NDRNG block is powered on.
 */
extern bool
rng_is_on(void);


/**
 *  \rng_start
 *  
 *  \return None
 *  
 *  \details Start NDRNG engine
 */
extern void
rng_start(void);

/**
 *  \rng_stop
 *  
 *  \return Void
 *  
 *  \details Stop NDRNG engine
 */
extern void
rng_stop(void);


/**
 *  \rng_get_fifo_level
 *  
 *  \return actual number of 32-bit words in the NDRNG FIFO.
 *  
 *  \details return the number of 32-bit words of random data 
 * currently in the FIFO.
 */
extern uint32_t
rng_get_fifo_level(void);


/**
 *  \rng_get_bytes
 *  
 *  \param [in] pbuff Output Buffer
 *  \param [in] nbytes Number of bytes to be read
 *  \return Number of bytes retrieved
 *  
 *  \details read bytes from the NDRNG FIFO
 */
extern uint32_t
rng_get_bytes(uint8_t* pbuff, uint32_t nbytes);


/**
 *  \rng_get_words
 *  
 *  \param [in] pwords Pointer to output buffer
 *  \param [in] nwords Number of words to read
 *  \return actual number of words read
 *  
 *  \details Details
 */
extern uint32_t
rng_get_words(uint32_t* pwords, uint32_t nwords);


/* AES */
/**
 *  \aes_hash_power
 *  
 *  \param [in] pwr_on Gate/Ungate clocks to block
 *  \return None
 *  
 *  \details Enable/Disable AES and HASH H/W Block
 */
extern void
aes_hash_power(uint8_t pwr_on);

/**
 *  \aes_hash_reset
 *  
 *  \return None
 *  
 *  \details Stop AES and HASH
 */
extern void
aes_hash_reset(void);

/**
 *  \aes_busy
 *  
 *  \return Is AES Block Running? True if yes, false Otherwise.
 *  
 *  \details Is AES Block Running?
 */
extern bool
aes_busy(void);


/**
 *  \aes_status
 *  
 *  \return Status of AES Block
 *  
 *  \details Returns the Status of AES Block
 */
extern uint32_t
aes_status(void);

/**
 *  \aes_done_status
 *  
 *  \param [in] hw_status Pointer to where the status value will be updated
 *  \return True if done, false otherwise
 *  
 *  \details Returns the done status of AES block
 */
extern bool
aes_done_status(uint32_t* hw_status);

/**
 *  \aes_stop
 *  
 *  \return Return aes_busy() Status
 *  
 *  \details Stop AES Operations
 */
extern bool
aes_stop(void);

/**
 *  \aes_start
 *  
 *  \param [in] ien Enable interrupts?
 *  \return None
 *  
 *  \details Start AES block with or without interrupts
 */
extern void
aes_start(bool ien);

/**
 *  \aes_iclr
 *  
 *  \return Status of the AES Block
 *  
 *  \details Clears AES Hash Interrupts
 */
extern uint32_t
aes_iclr(void);


/**
 *  \brief Brief
 *  
 *  \param [in] pkey Aligned buffer with AES Key
 *  \param [in] piv Aligned buffer with AES initialization
 *  \param [in] key_len AES_KEYLEN_128, AES_KEYLEN_192, AES_KEYLEN_256
 *  \param [in] msbf Most Significant Byte order first?
 *  \return AES_ERR_BAD_POINTER, AES_ERR_BAD_KEY_LEN, AES_OK
 *  
 *  \details Load AES Accelerator with key and optional Initialization vector
 */
extern uint8_t
aes_set_key(const uint32_t* pkey,
				const uint32_t* piv,
				uint8_t key_len, bool msbf);

/**
 *  \aes_crypt
 *  
 *  \param [in] data_in Aligned input data Buffer
 *  \param [in] data_out Aligned output data buffer
 *  \param [in] num_128bit_blocks Size of input in 16-byte blocks
 *  \param [in] mode AES Encryption/Decryption Mode
 *  \return AES_OK, AES_ERR_BAD_POINTER, 
 *  
 *  \details Program specified AES Operation using currently programmed key
 */
extern uint8_t
aes_crypt(const uint32_t* data_in,
			  uint32_t* data_out,
			  uint32_t num_128bit_blocks, uint8_t mode);


/* SHA */
#define SHA1_BLEN           (20u)
#define SHA1_WLEN           (5u)
#define SHA2_BLEN           (32u)
#define SHA2_WLEN           (8u)
#define SHA12_BLOCK_BLEN    (64u)
#define SHA12_BLOCK_WLEN    (16u)
#define SHA3_BLEN           (48u)
#define SHA3_WLEN           (12u)
#define SHA5_BLEN           (64u)
#define SHA5_WLEN           (16u)

/* return values */
#define SHA_RET_OK                      (0) /* OK */
#define SHA_RET_START                   (1) /* OK, SHA Engine started */
#define SHA_RET_ERROR                   (0x80)  /* b[7]==1 indicates an error */
#define SHA_RET_ERR_BUSY                (0x80)
#define SHA_RET_ERR_BAD_ADDR            (0x81)
#define SHA_RET_ERR_TIMEOUT             (0x82)
#define SHA_RET_ERR_MAX_LEN             (0x83)
#define SHA_RET_ERR_UNSUPPORTED         (0x84)

#define SHA_MODE_MD5    (0) // Not supported by HW
#define SHA_MODE_1      (1)
#define SHA_MODE_224    (2) // Not supported by HW
#define SHA_MODE_256    (3)
#define SHA_MODE_384    (4) // Not supported by HW
#define SHA_MODE_512    (5) // Not supported by HW

#define HASH_START_IEN      (1u)
#define HASH_START_NOIEN    (0u)

typedef union {
    uint32_t w[SHA2_WLEN];
    uint8_t  b[SHA2_BLEN];
} SHA12_DIGEST_U;


/*
 * !!! SHA-1 & SHA-256
 * HW Engine requires alignment >= 4-byte boundary !!!
 */
typedef struct sha12_context_s SHA12_CONTEXT_T;
struct sha12_context_s {
    SHA12_DIGEST_U hash;
    union {
        uint32_t w[(SHA12_BLOCK_WLEN) * 2];
        uint8_t  b[(SHA12_BLOCK_BLEN) * 2];
    } block;
    uint8_t mode;
    uint8_t block_len;
    uint8_t rsvd[2];
    uint32_t total_msg_len;
};


/**
 *  \hash_busy
 *  
 *  \return is busy? True if yes, Flase other wise
 *  
 *  \details returns the busy status of Hash Block
 */
extern bool hash_busy(void);

/**
 *  \hash_start
 *  
 *  \param [in] ien enable/disable interrupts
 *  \return None
 *  
 *  \details start hash block
 */
extern void
hash_start(bool ien);

/**
 *  \hash_done_status
 *  
 *  \param [in] hw_status Hash Status Register Value
 *  \return true if done, false otherwise
 *  
 *  \details reflects the done status of HASH black and updates
 *		status regsiter value into the input variable
 */
extern bool
hash_done_status(uint32_t* hw_status);

/**
 *  \sha12_init
 *  
 *  \param [in] psha12_ctx Data Structure for Input data and 	Output Digest
 *  \param [in] mode SHA_MODE_1 or SHA_MODE_256
 *  \return SHA_RET_ERR_BAD_ADDR, SHA_RET_ERR_UNSPPORTED ,SHA_RET_OK
 *  
 *  \details Initializes the Data structure provided
 */
extern uint8_t
sha12_init(SHA12_CONTEXT_T* psha12_ctx, uint8_t mode);

/**
 *  \sha12_update
 *  
 *  \param [in] psha12_ctx Data Structure for Input data and Output Digest
 *  \param [in] pdata Input Data to Hash Block
 *  \param [in] num_bytes Byte length of input data
 *  \return SHA_RET_ERR_BAD_ADDR, SHA_RET_ERR_BUSY, SHA_RET_ERR_MAX_LEN, SHA_RET_OK    
 *  
 *  \details Run hash block on data and if data greater than block size, put remaining bytes back into the data structure 
 */
extern uint8_t
sha12_update(SHA12_CONTEXT_T* psha12_ctx,
				 const uint32_t* pdata, uint32_t num_bytes);

/**
 *  \sha12_finalize
 *  
 *  \param [in] psha12_ctx Data Structure for Input data and Output Digest
 *  \return SHA_RET_ERR_BAD_ADDR, SHA_RET_ERR_BUSY ,SHA_RET_START  
 *  
 *  \details Apply FIPS padding to SHA256 and perform final hash calculation.
 */
extern uint8_t
sha12_finalize(SHA12_CONTEXT_T* psha12_ctx);

/**
 *  \sha256_pad_fill
 *  
 *  \param [in] pblock64 Aligned Memory buffer of atleast 64 bytes
 *  \param [in] msg_byte_len Length of Message in bytes
 *  \return None
 *  
 *  \details Zero and fill a 64-byte SHA256 pad block with FIP padding values
 */
extern void
sha256_pad_fill(uint32_t* pblock64, uint32_t msg_byte_len);


/**
 *  \sha256_raw
 *  
 *  \param [in] pdata Input Message
 *  \param [in] pdigest Pointer to biffer where digest will be written
 *  \param [in] num64byte_blocks size of input data in blocks
 *  \return SHA_RET_ERR_BAD_ADDR, SHA_RET_ERR_BUSY ,SHA_RET_START  
 *  
 *  \details Calculate SHA256 on data
 */
extern uint8_t
sha256_raw(uint32_t* pdata, uint32_t* pdigest, uint32_t num64byte_blocks);

/**
 *  \sha256_raw_init
 *  
 *  \param [in] psha256_digest Pointer to buffer where digest will be written
 *  \return None
 *  
 *  \details Initialize the SHA256 Digest data block
 */
extern void
sha256_raw_init(uint32_t* psha256_digest);

/**
 *  \sha256_raw_update
 *  
 *  \param [in] pdata Message on which HASH block is to be called
 *  \param [in] pdigest Pointer to where the digest will be stored
 *  \param [in] num64byte_blocks size of input data in blocks
 *  \return SHA_RET_ERR_BAD_ADDR, SHA_RET_ERR_BUSY ,SHA_RET_START
 *  
 *  \details run Hash block on data
 */
extern uint8_t
sha256_raw_update(uint32_t* pdata,
		              uint32_t* pdigest, uint32_t num64byte_blocks);

/**
 *  \hash_iclr
 *  
 *  \return Hash Block status
 *  
 *  \details Clear Hash Interrupt
 */
extern uint32_t
hash_iclr(void);


/**
 *  \sha_init
 *  
 *  \param [in] mode SHA_MODE_1, SHA_MODE_256, SHA_MODE_512
 *  \param [in] pdigest Address where digest will be stored
 *  \return * 	0 = Success 
 * 				1 = Hash Engine busy 
 * 				2 = Unsupported SHA operation 
 * 				3 = Bad digest pointer, NULL or mis-aligned. 
 *  \details 	Initialize Hash engine for SHA operation.
 * 				Programs supported SHA operation's initial value, digest address, 
 * 				and operation
 */
extern uint8_t
sha_init(uint8_t mode, uint32_t* pdigest);


/**
 *  \sha_update
 *  
 *  \param [in] pdata Input Data
 *  \param [in] nblocks Size in blocks
 *  \param [in] flags bit(0) - Clear Status?, bit(1) - Enable Interrupts?, bit(2) - Start?
 *  \return 0 - OK, 1 - Hash Busy, 2 - bad address for data, 3 - Buffer not aligned
 *  
 *  \details Run Hash block on data
 */
extern uint8_t
sha_update(uint32_t* pdata, uint16_t nblocks, uint8_t flags);


/**
 *  \sha_final
 *  
 *  \param [in] padbuf Buffer for padding (Twice block size)
 *  \param [in] total_msg_len Message length in bytes
 *  \param [in] prem Parameter_Description
 *  \param [in] flags bit(0) - Clear Status?, bit(1) - Enable Interrupts?, bit(2) - Start?
 *  \return 0 - OK, 1 - Hash Busy, 2 - bad address for data, 3 - Buffer not aligned
 *  
 *  \details Run final SHA Calculations and add padding
 */
extern uint8_t
sha_final(uint32_t* padbuf, uint32_t total_msg_len,
		      const uint8_t* prem, uint8_t flags);


/* PKE Miscellaneous */

#define PKE_RET_STARTED                         (0)
#define PKE_RET_OK                              (0)
#define PKE_RET_ERR_BUSY                        (1)
#define PKE_RET_ERR_BAD_PARAM                   (2)
#define PKE_RET_ERR_BAD_ADDR                    (3)
#define PKE_RET_ERR_UNKNOWN_OP                  (4)
#define PKE_RET_ERR_INVALID_BIT_LENGTH          (5)
#define PKE_RET_ERR_INVALID_MSG_LENGTH          (6)


/**
 *  \pke_power
 *  
 *  \param [in] pwr_on power on? 
 *  \return None
 *  
 *  \details Gate or Ungate power to PKE block
 */
extern void
pke_power(bool pwr_on);


/**
 *  \brief pke_reset
 *  
 *  \return None
 *  
 *  \details Reset PKE Block
 */
extern void
pke_reset(void);

/**
 *  \pke_status
 *  
 *  \return Return PKE Status register value
 *  
 *  \details Details
 */
extern uint32_t
pke_status(void);

/**
 *  \pke_done_status
 *  
 *  \param [in] hw_status POinter where PKE Status is updated
 *  \return True if done, false otherwise
 *  
 *  \details Returns the done status of PKE block
 */
extern bool
pke_done_status(uint32_t* hw_status);

/**
 *  \pke_start
 *  
 *  \param [in] ien Interrupt Enable?
 *  \return None
 *  
 *  \details Start PKE Block
 */
extern void
pke_start(bool ien);


/**
 *  \pke_busy
 *  
 *  \return Busy? True if busy, false otherwise
 *  
 *  \details Details
 */
extern bool
pke_busy(void);


/**
 *  \pke_clear_scm
 *  
 *  \return None
 *  
 *  \details Clear the Shared Crypto memory
 */
extern void
pke_clear_scm(void);

/**
 *  \pke_scm_clear_slot
 *  
 *  \param [in] slot_num Slot number in Shared Crypto Memory
 *  \return None
 *  
 *  \details Clear the specified slot in Shared Crypto Memory
 */
extern void
pke_scm_clear_slot(uint8_t slot_num);

/**
 *  \pke_read_scm 
 *  
 *  \param [in] dest Pointer to where the data is to be read
 *  \param [in] nbytes Number of bytes to be read
 *  \param [in] slot_num Slot number from which data is to be read
 *  \param [in] reverse_byte_order Reverse Byte order? True if yes, false otherwise
 *  \return Number of bytes Read
 *  
 *  \details Read data from specified slot number in Shared Crypto memory
 */
extern uint16_t
pke_read_scm(uint8_t* dest, uint16_t nbytes,
				 uint8_t slot_num, bool reverse_byte_order);


/**
 *  \pke_write_scm    
 *  
 *  \param [in] pdata Data to be written
 *  \param [in] num_bytes Number of bytes to be written
 *  \param [in] slot_num Slot number to which data ought to be written
 *  \param [in] reverse_byte_order Reverse Byte order? True if yes, false otherwise
 *  \return None
 *  
 *  \details Write data provided to specified slot in Shared Crypto Memory
 */
extern void
pke_write_scm(const void* pdata, uint16_t num_bytes,
				  uint8_t slot_num, uint8_t reverse_byte_order);

/* PKE RSA */

/**
 *  \ rsa_load_key
 *  
 *  \param [in] rsa_bit_len 1024, 2048
 *  \param [in] private_exponent Pointer to private exponent
 *  \param [in] public_modulus Pointer to Public modulus
 *  \param [in] public_exponent Pointer to Public Exponent
 *  \param [in] public_exponent_byte_len Length in bytes of Public Exponent
 *  \param [in] msbf Reverse Byte order? True if yes, false otherwise
 *  \return PKE_RET_ERR_BUSY, PKE_RET_ERR_INVALID_BIT_LENGTH, PKE_RET_OK
 *  
 *  \details Load RSA keys into Crypto memory
 */
extern uint8_t
rsa_load_key(uint16_t rsa_bit_len,
					 const uint8_t* private_exponent,
					 const uint8_t* public_modulus,
					 const uint8_t* public_exponent,
					 uint16_t public_exponent_byte_len,
					 bool msbf);

						
/**
 *  \ rsa_encrypt
 *  
 *  \param [in] rsa_bit_len 1024, 2048
 *  \param [in] mesg Message to be encrypted
 *  \param [in] mlen length of message
 *  \param [in] flags bit[0]=0(do not start), 1(start after programming), bit[4] = byte order: 0 = Least significant byte first, 1 = Most significant byte first, bit[1]=0(do not enable interrupt), 1(enable interrupt before starting) 
 *  \return PKE_RET_ERR_BAD_ADDR, PKE_RET_ERR_BUSY, PKE_RET_ERR_INVALID_MSG_LENGTH, PKE_RET_ERR_INVALID_BIT_LENGTH, PKE_RET_OK
 *  
 *  \details Encrypt provided message. Load Keys before this function is called
 */
extern uint8_t
rsa_encrypt(uint16_t rsa_bit_len,
					const uint8_t* mesg,
					uint16_t mlen,
					uint8_t flags);
					


/**
 *  \ rsa_decrypt
 *  
 *  \param [in] rsa_bit_len 1024, 2048
 *  \param [in] encrypted_mesg Encrypted data
 *  \param [in] mlen length of encrypted message
 *  \param [in] flags flags bit[0]=0(do not start), 1(start after programming), bit[4] = byte order: 0 = Least significant byte first, 1 = Most significant byte first, bit[1]=0(do not enable interrupt), 1(enable interrupt before starting)
 *  \return PKE_RET_ERR_BAD_ADDR, PKE_RET_ERR_BUSY, PKE_RET_ERR_INVALID_MSG_LENGTH, PKE_RET_ERR_INVALID_BIT_LENGTH, PKE_RET_OK
 *  
 *  \details Perform decryption on provided encrypted message. load keys before calling this function
 */
extern uint8_t
rsa_decrypt(uint16_t rsa_bit_len,
					const uint8_t* encrypted_mesg,
					uint16_t mlen,
					uint8_t flags);

					

#ifdef __cplusplus
}
#endif


#endif /* INCLUDE_CEC1302_CRYPTO_API_H_ */
