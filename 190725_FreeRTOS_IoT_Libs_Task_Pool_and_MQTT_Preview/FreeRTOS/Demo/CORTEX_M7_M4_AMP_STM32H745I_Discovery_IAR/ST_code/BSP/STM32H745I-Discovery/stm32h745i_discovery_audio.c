/**
  ******************************************************************************
  * @file    stm32h745i_discovery_audio.c
  * @author  MCD Application Team
  * @brief   This file provides the Audio driver for the STM32H745I-DISCOVERY
  *          board.
  @verbatim
  How To use this driver:
  -----------------------
   + This driver supports STM32H7xx devices on STM32H745I-DISCOVERY (MB1248) Discovery boards.
   + Call the function BSP_AUDIO_OUT_Init(
                                    OutputDevice: physical output mode (OUTPUT_DEVICE_SPEAKER,
                                                  OUTPUT_DEVICE_HEADPHONE or OUTPUT_DEVICE_BOTH)
                                    Volume      : Initial volume to be set (0 is min (mute), 100 is max (100%)
                                    AudioFreq   : Audio frequency in Hz (8000, 16000, 22500, 32000...)
                                                  this parameter is relative to the audio file/stream type.
                                   )
      This function configures all the hardware required for the audio application (codec, I2C, SAI,
      GPIOs, DMA and interrupt if needed). This function returns AUDIO_OK if configuration is OK.
      If the returned value is different from AUDIO_OK or the function is stuck then the communication with
      the codec has failed (try to un-plug the power or reset device in this case).
      - OUTPUT_DEVICE_SPEAKER  : only speaker will be set as output for the audio stream.
      - OUTPUT_DEVICE_HEADPHONE: only headphones will be set as output for the audio stream.
      - OUTPUT_DEVICE_BOTH     : both Speaker and Headphone are used as outputs for the audio stream
                                 at the same time.
      Note. On STM32H745I-DISCOVERY SAI_DMA is configured in CIRCULAR mode. Due to this the application
        does NOT need to call BSP_AUDIO_OUT_ChangeBuffer() to assure streaming.
   + Call the function BSP_AUDIO_OUT_Play(
                                  pBuffer: pointer to the audio data file address
                                  Size   : size of the buffer to be sent in Bytes
                                 )
      to start playing (for the first time) from the audio file/stream.
   + Call the function BSP_AUDIO_OUT_Pause() to pause playing
   + Call the function BSP_AUDIO_OUT_Resume() to resume playing.
       Note. After calling BSP_AUDIO_OUT_Pause() function for pause, only BSP_AUDIO_OUT_Resume() should be called
          for resume (it is not allowed to call BSP_AUDIO_OUT_Play() in this case).
       Note. This function should be called only when the audio file is played or paused (not stopped).
   + For each mode, you may need to implement the relative callback functions into your code.
      The Callback functions are named BSP_AUDIO_OUT_XXX_CallBack() and only their prototypes are declared in
      the stm32h745i_discovery_audio.h file. (refer to the example for more details on the callbacks implementations)
   + To Stop playing, to modify the volume level, the frequency, the audio frame slot,
      the device output mode the mute or the stop, use the functions: BSP_AUDIO_OUT_SetVolume(),
      AUDIO_OUT_SetFrequency(), BSP_AUDIO_OUT_SetAudioFrameSlot(), BSP_AUDIO_OUT_SetOutputMode(),
      BSP_AUDIO_OUT_SetMute() and BSP_AUDIO_OUT_Stop().

   + Call the function BSP_AUDIO_IN_Init(
                                    AudioFreq: Audio frequency in Hz (8000, 16000, 22500, 32000...)
                                                  this parameter is relative to the audio file/stream type.
                                    BitRes: Bit resolution fixed to 16bit
                                    ChnlNbr: Number of channel to be configured for the DFSDM peripheral
                                   )
      This function configures all the hardware required for the audio in application (channels,
      Clock source for SAI PDM periphiral, GPIOs, DMA and interrupt if needed).
      This function returns AUDIO_OK if configuration is OK.If the returned value is different from AUDIO_OK then
      the configuration should be wrong.
   + Call the function BSP_AUDIO_IN_AllocScratch(
                                        pScratch: pointer to scratch tables
                                        size: size of scratch buffer)
     This function must be called before BSP_AUDIO_IN_RECORD() to allocate buffer scratch for each DFSDM channel
     and its size.
     Note: These buffers scratch are used as intermidiate buffers to collect data within final record buffer.
           size is the total size of the four buffers scratch; If size is 512 then the size of each is 128.
           This function must be called after BSP_AUDIO_IN_Init()
   + Call the function BSP_AUDIO_IN_RECORD(
                                  pBuf: pointer to the recorded audio data file address
                                  Size: size of the buffer to be written in Bytes
                                 )
      to start recording from microphones.

   + Call the function BSP_AUDIO_IN_Pause() to pause recording
   + Call the function BSP_AUDIO_IN_Resume() to recording playing.
       Note. After calling BSP_AUDIO_IN_Pause() function for pause, only BSP_AUDIO_IN_Resume() should be called
          for resume (it is not allowed to call BSP_AUDIO_IN_RECORD() in this case).
   + Call the function BSP_AUDIO_IN_Stop() to stop recording
   + For each mode, you may need to implement the relative callback functions into your code.
      The Callback functions are named BSP_AUDIO_IN_XXX_CallBack() and only their prototypes are declared in
      the stm32h745i_discovery_audio.h file. (refer to the example for more details on the callbacks implementations)
   + Call the function BSP_AUDIO_IN_SelectInterface(uint32_t Interface) to select one of the two interfaces
     available on the STM32H745I-Discovery board: SAI or PDM. This function is to be called before BSP_AUDIO_IN_InitEx().
   + Call the function BSP_AUDIO_IN_GetInterface() to get the current used interface.
   + Call the function BSP_AUDIO_IN_PDMToPCM_Init(uint32_t AudioFreq, uint32_t ChnlNbrIn, uint32_t ChnlNbrOut)
     to init PDM filters if the libPDMFilter is used for audio data filtering.
   + Call the function BSP_AUDIO_IN_PDMToPCM(uint16_t* PDMBuf, uint16_t* PCMBuf) to filter PDM data to PCM format
     if the libPDMFilter library is used for audio data filtering.

  Driver architecture:
  --------------------
   + This driver provides the High Audio Layer: consists of the function API exported in the stm32h745i_discovery_audio.h file
     (BSP_AUDIO_OUT_Init(), BSP_AUDIO_OUT_Play() ...)
   + This driver provide also the Media Access Layer (MAL): which consists of functions allowing to access the media containing/
     providing the audio file/stream. These functions are also included as local functions into
     the stm32h745i_discovery_audio.c file (DFSDMx_Init(), DFSDMx_DeInit(), SAIx_Init() and SAIx_DeInit())

  Known Limitations:
  ------------------
   1- If the TDM Format used to play in parallel 2 audio Stream (the first Stream is configured in codec SLOT0 and second
      Stream in SLOT1) the Pause/Resume, volume and mute feature will control the both streams.
   2- Parsing of audio file is not implemented (in order to determine audio file properties: Mono/Stereo, Data size,
      File size, Audio Frequency, Audio Data header size ...). The configuration is fixed for the given audio file.
   3- Supports only Stereo audio streaming.
   4- Supports only 16-bits audio data size.
  @endverbatim
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright (c) 2019 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */
/* Includes ------------------------------------------------------------------*/
#include "stm32h745i_discovery_audio.h"

/** @addtogroup BSP
  * @{
  */

/** @addtogroup STM32H745I_DISCOVERY
  * @{
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO STM32H745I_DISCOVERY_AUDIO
  * @brief This file includes the low layer driver for wm8994 Audio Codec
  *        available on STM32H745I-DISCOVERY discovery board(MB1248).
  * @{
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO_Private_Variables Private Variables
  * @{
  */
/* PLAY */
AUDIO_DrvTypeDef                *audio_drv;
SAI_HandleTypeDef               haudio_out_sai;
SAI_HandleTypeDef               haudio_in_sai;

/* RECORD */
AUDIOIN_ContextTypeDef          hAudioIn;

/* Audio in Volume value */
__IO uint16_t                   AudioInVolume = DEFAULT_AUDIO_IN_VOLUME;

/* PDM filters params */
PDM_Filter_Handler_t  PDM_FilterHandler[2];
PDM_Filter_Config_t   PDM_FilterConfig[2];

/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO_Private_Function_Prototypes OUT Private Function Prototypes
  * @{
  */
static void SAIx_Out_Init(uint32_t SaiOutMode, uint32_t SlotActive, uint32_t AudioFreq);
static void SAIx_Out_DeInit(SAI_HandleTypeDef *hsai);

/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO_IN_Private_Function_Prototypes IN Private Function Prototypes
  * @{
  */
static void SAIx_In_MspInit(SAI_HandleTypeDef *hsai, void *Params);
static void SAIx_In_MspDeInit(SAI_HandleTypeDef *hsai, void *Params);
static void SAIx_In_Init(uint32_t SaiInMode, uint32_t SlotActive, uint32_t AudioFreq);
static void SAIx_In_DeInit(SAI_HandleTypeDef *hsai);

/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO_OUT_Exported_Functions OUT Exported Functions
  * @{
  */

/**
  * @brief  Configures the audio Out peripheral.
  * @param  OutputDevice: OUTPUT_DEVICE_SPEAKER, OUTPUT_DEVICE_HEADPHONE,
  *                       or OUTPUT_DEVICE_BOTH.
  * @param  Volume: Initial volume level (from 0 (Mute) to 100 (Max))
  * @param  AudioFreq: Audio frequency used to play the audio stream.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_Init(uint16_t OutputDevice, uint8_t Volume, uint32_t AudioFreq)
{
  uint8_t ret = AUDIO_ERROR;
  uint32_t deviceid = 0x00;
  uint32_t slot_active;

  /* Initialize SAI2 sub_block A as MASTER TX */
  haudio_out_sai.Instance = AUDIO_OUT_SAIx;

  /* Disable SAI */
  SAIx_Out_DeInit(&haudio_out_sai);

  /* PLL clock is set depending by the AudioFreq (44.1khz vs 48khz groups) */
  BSP_AUDIO_OUT_ClockConfig(&haudio_out_sai, AudioFreq, NULL);

  /* SAI data transfer preparation:
  Prepare the Media to be used for the audio transfer from memory to SAI peripheral */

  if(HAL_SAI_GetState(&haudio_out_sai) == HAL_SAI_STATE_RESET)
  {
    /* Init the SAI MSP: this __weak function can be redefined by the application*/
    BSP_AUDIO_OUT_MspInit(&haudio_out_sai, NULL);
  }

  /* Init SAI as master RX output */
  slot_active = CODEC_AUDIOFRAME_SLOT_0123;
  SAIx_Out_Init(SAI_MODEMASTER_TX, slot_active, AudioFreq);

  /* wm8994 codec initialization */
  deviceid = wm8994_drv.ReadID(AUDIO_I2C_ADDRESS);

  if((deviceid) == WM8994_ID)
  {
    /* Reset the Codec Registers */
    wm8994_drv.Reset(AUDIO_I2C_ADDRESS);
    /* Initialize the audio driver structure */
    audio_drv = &wm8994_drv;
    ret = AUDIO_OK;
  }
  else
  {
    ret = AUDIO_ERROR;
  }

  if(ret == AUDIO_OK)
  {
    /* Initialize the codec internal registers */
    audio_drv->Init(AUDIO_I2C_ADDRESS, OutputDevice, Volume, AudioFreq);
  }

  return ret;
}

/**
  * @brief  Starts playing audio stream from a data buffer for a determined size.
  * @param  pBuffer: Pointer to the buffer
  * @param  Size: Number of audio data BYTES.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_Play(uint16_t* pBuffer, uint32_t Size)
{
  /* Call the audio Codec Play function */
  if(audio_drv->Play(AUDIO_I2C_ADDRESS, pBuffer, Size) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    /* Update the Media layer and enable it for play */
    HAL_SAI_Transmit_DMA(&haudio_out_sai, (uint8_t*) pBuffer, DMA_MAX(Size / AUDIODATA_SIZE));

    return AUDIO_OK;
  }
}

/**
  * @brief  Sends n-Bytes on the SAI interface.
  * @param  pData: pointer on data address
  * @param  Size: number of data to be written
  * @retval None
  */
void BSP_AUDIO_OUT_ChangeBuffer(uint16_t *pData, uint16_t Size)
{
   HAL_SAI_Transmit_DMA(&haudio_out_sai, (uint8_t*) pData, Size);
}

/**
  * @brief  This function Pauses the audio file stream. In case
  *         of using DMA, the DMA Pause feature is used.
  * @warning When calling BSP_AUDIO_OUT_Pause() function for pause, only
  *          BSP_AUDIO_OUT_Resume() function should be called for resume (use of BSP_AUDIO_OUT_Play()
  *          function for resume could lead to unexpected behaviour).
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_Pause(void)
{
  /* Call the Audio Codec Pause/Resume function */
  if(audio_drv->Pause(AUDIO_I2C_ADDRESS) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    /* Call the Media layer pause function */
    HAL_SAI_DMAPause(&haudio_out_sai);

    /* Return AUDIO_OK when all operations are correctly done */
    return AUDIO_OK;
  }
}

/**
  * @brief   Resumes the audio file stream.
  * @warning When calling BSP_AUDIO_OUT_Pause() function for pause, only
  *          BSP_AUDIO_OUT_Resume() function should be called for resume (use of BSP_AUDIO_OUT_Play()
  *          function for resume could lead to unexpected behaviour).
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_Resume(void)
{
  /* Call the Audio Codec Pause/Resume function */
  if(audio_drv->Resume(AUDIO_I2C_ADDRESS) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    /* Call the Media layer pause/resume function */
    HAL_SAI_DMAResume(&haudio_out_sai);

    /* Return AUDIO_OK when all operations are correctly done */
    return AUDIO_OK;
  }
}

/**
  * @brief  Stops audio playing and Power down the Audio Codec.
  * @param  Option: could be one of the following parameters
  *           - CODEC_PDWN_SW: for software power off (by writing registers).
  *                            Then no need to reconfigure the Codec after power on.
  *           - CODEC_PDWN_HW: completely shut down the codec (physically).
  *                            Then need to reconfigure the Codec after power on.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_Stop(uint32_t Option)
{
  /* Call the Media layer stop function */
  HAL_SAI_DMAStop(&haudio_out_sai);

  /* Call Audio Codec Stop function */
  if(audio_drv->Stop(AUDIO_I2C_ADDRESS, Option) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    if(Option == CODEC_PDWN_HW)
    {
      /* Wait at least 100us */
      HAL_Delay(1);
    }
    /* Return AUDIO_OK when all operations are correctly done */
    return AUDIO_OK;
  }
}

/**
  * @brief  Controls the current audio volume level.
  * @param  Volume: Volume level to be set in percentage from 0% to 100% (0 for
  *         Mute and 100 for Max volume level).
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_SetVolume(uint8_t Volume)
{
  /* Call the codec volume control function with converted volume value */
  if(audio_drv->SetVolume(AUDIO_I2C_ADDRESS, Volume) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    /* Return AUDIO_OK when all operations are correctly done */
    return AUDIO_OK;
  }
}

/**
  * @brief  Enables or disables the MUTE mode by software
  * @param  Cmd: Could be AUDIO_MUTE_ON to mute sound or AUDIO_MUTE_OFF to
  *         unmute the codec and restore previous volume level.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_SetMute(uint32_t Cmd)
{
  /* Call the Codec Mute function */
  if(audio_drv->SetMute(AUDIO_I2C_ADDRESS, Cmd) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    /* Return AUDIO_OK when all operations are correctly done */
    return AUDIO_OK;
  }
}

/**
  * @brief  Switch dynamically (while audio file is played) the output target
  *         (speaker or headphone).
  * @param  Output: The audio output target: OUTPUT_DEVICE_SPEAKER,
  *         OUTPUT_DEVICE_HEADPHONE or OUTPUT_DEVICE_BOTH
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_OUT_SetOutputMode(uint8_t Output)
{
  /* Call the Codec output device function */
  if(audio_drv->SetOutputMode(AUDIO_I2C_ADDRESS, Output) != 0)
  {
    return AUDIO_ERROR;
  }
  else
  {
    /* Return AUDIO_OK when all operations are correctly done */
    return AUDIO_OK;
  }
}

/**
  * @brief  Updates the audio frequency.
  * @param  AudioFreq: Audio frequency used to play the audio stream.
  * @note   This API should be called after the BSP_AUDIO_OUT_Init() to adjust the
  *         audio frequency.
  * @retval None
  */
void BSP_AUDIO_OUT_SetFrequency(uint32_t AudioFreq)
{
  /* PLL clock is set depending by the AudioFreq (44.1khz vs 48khz groups) */
  BSP_AUDIO_OUT_ClockConfig(&haudio_out_sai, AudioFreq, NULL);

  /* Disable SAI peripheral to allow access to SAI internal registers */
  __HAL_SAI_DISABLE(&haudio_out_sai);

  /* Update the SAI audio frequency configuration */
  haudio_out_sai.Init.AudioFrequency = AudioFreq;
  HAL_SAI_Init(&haudio_out_sai);

  /* Enable SAI peripheral to generate MCLK */
  __HAL_SAI_ENABLE(&haudio_out_sai);
}

/**
  * @brief  Updates the Audio frame slot configuration.
  * @param  AudioFrameSlot: specifies the audio Frame slot
  * @note   This API should be called after the BSP_AUDIO_OUT_Init() to adjust the
  *         audio frame slot.
  * @retval None
  */
void BSP_AUDIO_OUT_SetAudioFrameSlot(uint32_t AudioFrameSlot)
{
  /* Disable SAI peripheral to allow access to SAI internal registers */
  __HAL_SAI_DISABLE(&haudio_out_sai);

  /* Update the SAI audio frame slot configuration */
  haudio_out_sai.SlotInit.SlotActive = AudioFrameSlot;
  HAL_SAI_Init(&haudio_out_sai);

  /* Enable SAI peripheral to generate MCLK */
  __HAL_SAI_ENABLE(&haudio_out_sai);
}

/**
  * @brief  De-initializes the audio out peripheral.
  * @retval None
  */
void BSP_AUDIO_OUT_DeInit(void)
{
  SAIx_Out_DeInit(&haudio_out_sai);
  /* DeInit the SAI MSP : this __weak function can be rewritten by the application */
  BSP_AUDIO_OUT_MspDeInit(&haudio_out_sai, NULL);
}

/**
  * @brief  Manages the DMA full Transfer complete event.
  * @retval None
  */
__weak void BSP_AUDIO_OUT_TransferComplete_CallBack(void)
{
}

/**
  * @brief  Manages the DMA Half Transfer complete event.
  * @retval None
  */
__weak void BSP_AUDIO_OUT_HalfTransfer_CallBack(void)
{
}

/**
  * @brief  Manages the DMA FIFO error event.
  * @retval None
  */
__weak void BSP_AUDIO_OUT_Error_CallBack(void)
{
}

/**
  * @brief  Initializes BSP_AUDIO_OUT MSP.
  * @param  hsai: SAI handle
  * @param  Params: pointer on additional configuration parameters, can be NULL.
  * @retval None
  */
__weak void BSP_AUDIO_OUT_MspInit(SAI_HandleTypeDef *hsai, void *Params)
{
  static DMA_HandleTypeDef hdma_sai_tx;
  GPIO_InitTypeDef  gpio_init_structure;

  /* Enable SAI clock */
  AUDIO_OUT_SAIx_CLK_ENABLE();

  /* CODEC_SAI pins configuration: FS, SCK and SD pins */
  /* Enable FS, SCK and SD clocks */
  AUDIO_OUT_SAIx_SD_FS_CLK_ENABLE();
  /* Enable FS, SCK and SD pins */
  gpio_init_structure.Pin = AUDIO_OUT_SAIx_FS_PIN | AUDIO_OUT_SAIx_SCK_PIN | AUDIO_OUT_SAIx_SD_PIN;
  gpio_init_structure.Mode = GPIO_MODE_AF_PP;
  gpio_init_structure.Pull = GPIO_NOPULL;
  gpio_init_structure.Speed = GPIO_SPEED_FREQ_VERY_HIGH;
  gpio_init_structure.Alternate = AUDIO_OUT_SAIx_AF;
  HAL_GPIO_Init(AUDIO_OUT_SAIx_SD_FS_SCK_GPIO_PORT, &gpio_init_structure);

  /* Enable MCLK clock */
  AUDIO_OUT_SAIx_MCLK_ENABLE();
  /* Enable MCLK pin */
  gpio_init_structure.Pin = AUDIO_OUT_SAIx_MCLK_PIN;
  HAL_GPIO_Init(AUDIO_OUT_SAIx_MCLK_GPIO_PORT, &gpio_init_structure);

  /* Enable the DMA clock */
  AUDIO_OUT_SAIx_DMAx_CLK_ENABLE();

  if(hsai->Instance == AUDIO_OUT_SAIx)
  {
    /* Configure the hdma_saiTx handle parameters */
    hdma_sai_tx.Init.Request             = AUDIO_OUT_SAIx_DMAx_REQUEST;
    hdma_sai_tx.Init.Direction           = DMA_MEMORY_TO_PERIPH;
    hdma_sai_tx.Init.PeriphInc           = DMA_PINC_DISABLE;
    hdma_sai_tx.Init.MemInc              = DMA_MINC_ENABLE;
    hdma_sai_tx.Init.PeriphDataAlignment = AUDIO_OUT_SAIx_DMAx_PERIPH_DATA_SIZE;
    hdma_sai_tx.Init.MemDataAlignment    = AUDIO_OUT_SAIx_DMAx_MEM_DATA_SIZE;
    hdma_sai_tx.Init.Mode                = DMA_CIRCULAR;
    hdma_sai_tx.Init.Priority            = DMA_PRIORITY_HIGH;
    hdma_sai_tx.Init.FIFOMode            = DMA_FIFOMODE_ENABLE;
    hdma_sai_tx.Init.FIFOThreshold       = DMA_FIFO_THRESHOLD_FULL;
    hdma_sai_tx.Init.MemBurst            = DMA_MBURST_SINGLE;
    hdma_sai_tx.Init.PeriphBurst         = DMA_PBURST_SINGLE;

    hdma_sai_tx.Instance = AUDIO_OUT_SAIx_DMAx_STREAM;

    /* Associate the DMA handle */
    __HAL_LINKDMA(hsai, hdmatx, hdma_sai_tx);

    /* Deinitialize the Stream for new transfer */
    HAL_DMA_DeInit(&hdma_sai_tx);

    /* Configure the DMA Stream */
    HAL_DMA_Init(&hdma_sai_tx);
  }

  /* SAI DMA IRQ Channel configuration */
  HAL_NVIC_SetPriority(AUDIO_OUT_SAIx_DMAx_IRQ, AUDIO_OUT_IRQ_PREPRIO, 0);
  HAL_NVIC_EnableIRQ(AUDIO_OUT_SAIx_DMAx_IRQ);
}

/**
  * @brief  Deinitializes SAI MSP.
  * @param  hsai: SAI handle
  * @param  Params: pointer on additional configuration parameters, can be NULL.
  * @retval None
  */
__weak void BSP_AUDIO_OUT_MspDeInit(SAI_HandleTypeDef *hsai, void *Params)
{
    GPIO_InitTypeDef  gpio_init_structure;

    /* SAI DMA IRQ Channel deactivation */
    HAL_NVIC_DisableIRQ(AUDIO_OUT_SAIx_DMAx_IRQ);

    if(hsai->Instance == AUDIO_OUT_SAIx)
    {
      /* Deinitialize the DMA stream */
      HAL_DMA_DeInit(hsai->hdmatx);
    }

    /* Disable SAI peripheral */
    __HAL_SAI_DISABLE(hsai);

    /* Deactivates CODEC_SAI pins FS, SCK, MCK and SD by putting them in input mode */
    gpio_init_structure.Pin = AUDIO_OUT_SAIx_FS_PIN | AUDIO_OUT_SAIx_SCK_PIN | AUDIO_OUT_SAIx_SD_PIN;
    HAL_GPIO_DeInit(AUDIO_OUT_SAIx_SD_FS_SCK_GPIO_PORT, gpio_init_structure.Pin);

    gpio_init_structure.Pin = AUDIO_OUT_SAIx_MCLK_PIN;
    HAL_GPIO_DeInit(AUDIO_OUT_SAIx_MCLK_GPIO_PORT, gpio_init_structure.Pin);

    /* Disable SAI clock */
    AUDIO_OUT_SAIx_CLK_DISABLE();

    /* GPIO pins clock and DMA clock can be shut down in the applic
       by surcharging this __weak function */
}

/**
  * @brief  Clock Config.
  * @param  hsai: might be required to set audio peripheral predivider if any.
  * @param  AudioFreq: Audio frequency used to play the audio stream.
  * @param  Params: pointer on additional configuration parameters, can be NULL.
  * @note   This API is called by BSP_AUDIO_OUT_Init() and BSP_AUDIO_OUT_SetFrequency()
  *         Being __weak it can be overwritten by the application
  * @retval None
  */
__weak void BSP_AUDIO_OUT_ClockConfig(SAI_HandleTypeDef *hsai, uint32_t AudioFreq, void *Params)
{
  RCC_PeriphCLKInitTypeDef rcc_ex_clk_init_struct;

  HAL_RCCEx_GetPeriphCLKConfig(&rcc_ex_clk_init_struct);

  /* Set the PLL configuration according to the audio frequency */
  if((AudioFreq == AUDIO_FREQUENCY_11K) || (AudioFreq == AUDIO_FREQUENCY_22K) || (AudioFreq == AUDIO_FREQUENCY_44K))
  {
    /* SAI clock config:
       PLL2_VCO Input = HSE_VALUE/PLL2M = 1 Mhz
       PLL2_VCO Output = PLL2_VCO Input * PLL2N = 429 Mhz
       SAI_CLK_x = PLL2_VCO Output/PLL2P = 429/38 = 11.289 Mhz */
    rcc_ex_clk_init_struct.PeriphClockSelection = RCC_PERIPHCLK_SAI2;
    rcc_ex_clk_init_struct.Sai23ClockSelection = RCC_SAI2CLKSOURCE_PLL2;
    rcc_ex_clk_init_struct.PLL2.PLL2P = 38;
    rcc_ex_clk_init_struct.PLL2.PLL2Q = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2R = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2N = 429;
    rcc_ex_clk_init_struct.PLL2.PLL2M = 25;
    HAL_RCCEx_PeriphCLKConfig(&rcc_ex_clk_init_struct);
  }
  else /* AUDIO_FREQUENCY_8K, AUDIO_FREQUENCY_16K, AUDIO_FREQUENCY_48K, AUDIO_FREQUENCY_96K */
  {
    /* SAI clock config:
       PLL2_VCO Input = HSE_VALUE/PLL2M = 1 Mhz
       PLL2_VCO Output = PLL2_VCO Input * PLL2N = 344 Mhz
       SAI_CLK_x = PLL2_VCO Output/PLL2P = 344/7 = 49.142 Mhz */
    rcc_ex_clk_init_struct.PeriphClockSelection = RCC_PERIPHCLK_SAI2;
    rcc_ex_clk_init_struct.Sai23ClockSelection = RCC_SAI2CLKSOURCE_PLL2;
    rcc_ex_clk_init_struct.PLL2.PLL2P = 7;
    rcc_ex_clk_init_struct.PLL2.PLL2Q = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2R = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2N = 344;
    rcc_ex_clk_init_struct.PLL2.PLL2M = 25;
    HAL_RCCEx_PeriphCLKConfig(&rcc_ex_clk_init_struct);
  }
}
/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO_OUT_Private_Functions OUT Private Functions
  * @{
  */

/*******************************************************************************
                            HAL Callbacks
*******************************************************************************/
/**
  * @brief  Tx Transfer completed callbacks.
  * @param  hsai: SAI handle
  * @retval None
  */
void HAL_SAI_TxCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* Manage the remaining file size and new address offset: This function
     should be coded by user (its prototype is already declared in stm32h745i_discovery_audio.h) */
  BSP_AUDIO_OUT_TransferComplete_CallBack();
}

/**
  * @brief  Tx Half Transfer completed callbacks.
  * @param  hsai: SAI handle
  * @retval None
  */
void HAL_SAI_TxHalfCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* Manage the remaining file size and new address offset: This function
     should be coded by user (its prototype is already declared in stm32h745i_discovery_audio.h) */
  BSP_AUDIO_OUT_HalfTransfer_CallBack();
}

/**
  * @brief  SAI error callbacks.
  * @param  hsai: SAI handle
  * @retval None
  */
void HAL_SAI_ErrorCallback(SAI_HandleTypeDef *hsai)
{
  if(hsai->Instance == AUDIO_OUT_SAIx)
  {
    BSP_AUDIO_OUT_Error_CallBack();
  }
  else
  {
    BSP_AUDIO_IN_Error_CallBack();
  }
}

/*******************************************************************************
                            Static Functions
*******************************************************************************/

/**
  * @brief  Initializes the Audio Codec audio interface (SAI).
  * @param  SaiOutMode: Audio mode to be configured for the SAI peripheral.
  * @param  SlotActive: Audio active slot to be configured for the SAI peripheral.
  * @param  AudioFreq: Audio frequency to be configured for the SAI peripheral.
  * @note   The default SlotActive configuration is set to CODEC_AUDIOFRAME_SLOT_0123
  *         and user can update this configuration using
  * @retval None
  */
static void SAIx_Out_Init(uint32_t SaiOutMode, uint32_t SlotActive, uint32_t AudioFreq)
{
  /* Disable SAI peripheral to allow access to SAI internal registers */
  __HAL_SAI_DISABLE(&haudio_out_sai);

  /* Configure SAI_Block_x
  LSBFirst: Disabled
  DataSize: 16 */
  haudio_out_sai.Init.MonoStereoMode = SAI_STEREOMODE;
  haudio_out_sai.Init.AudioFrequency = AudioFreq;
  haudio_out_sai.Init.AudioMode = SaiOutMode;
  haudio_out_sai.Init.NoDivider = SAI_MASTERDIVIDER_ENABLE;
  haudio_out_sai.Init.Protocol = SAI_FREE_PROTOCOL;
  haudio_out_sai.Init.DataSize = SAI_DATASIZE_16;
  haudio_out_sai.Init.FirstBit = SAI_FIRSTBIT_MSB;
  haudio_out_sai.Init.ClockStrobing = SAI_CLOCKSTROBING_RISINGEDGE;
  haudio_out_sai.Init.Synchro = SAI_ASYNCHRONOUS;
  haudio_out_sai.Init.OutputDrive = SAI_OUTPUTDRIVE_ENABLE;
  haudio_out_sai.Init.FIFOThreshold = SAI_FIFOTHRESHOLD_1QF;
  haudio_out_sai.Init.SynchroExt     = SAI_SYNCEXT_DISABLE;
  haudio_out_sai.Init.CompandingMode = SAI_NOCOMPANDING;
  haudio_out_sai.Init.TriState       = SAI_OUTPUT_NOTRELEASED;
  haudio_out_sai.Init.Mckdiv         = 0;
  haudio_out_sai.Init.MckOverSampling = SAI_MCK_OVERSAMPLING_DISABLE;
  haudio_out_sai.Init.PdmInit.Activation = DISABLE;
  haudio_out_sai.Init.PdmInit.ClockEnable = 0;
  haudio_out_sai.Init.PdmInit.MicPairsNbr = 0;

  /* Configure SAI_Block_x Frame
  Frame Length: 64
  Frame active Length: 32
  FS Definition: Start frame + Channel Side identification
  FS Polarity: FS active Low
  FS Offset: FS asserted one bit before the first bit of slot 0 */
  haudio_out_sai.FrameInit.FrameLength = 128;
  haudio_out_sai.FrameInit.ActiveFrameLength = 64;
  haudio_out_sai.FrameInit.FSDefinition = SAI_FS_CHANNEL_IDENTIFICATION;
  haudio_out_sai.FrameInit.FSPolarity = SAI_FS_ACTIVE_LOW;
  haudio_out_sai.FrameInit.FSOffset = SAI_FS_BEFOREFIRSTBIT;

  /* Configure SAI Block_x Slot
  Slot First Bit Offset: 0
  Slot Size  : 16
  Slot Number: 4
  Slot Active: All slot actives */
  haudio_out_sai.SlotInit.FirstBitOffset = 0;
  haudio_out_sai.SlotInit.SlotSize = SAI_SLOTSIZE_DATASIZE;
  haudio_out_sai.SlotInit.SlotNumber = 4;
  haudio_out_sai.SlotInit.SlotActive = SlotActive;
  HAL_SAI_Init(&haudio_out_sai);

  /* Enable SAI peripheral to generate MCLK */
  __HAL_SAI_ENABLE(&haudio_out_sai);
}

/**
  * @brief  Deinitializes the Audio Codec audio interface (SAI).
  * @retval None
  */
static void SAIx_Out_DeInit(SAI_HandleTypeDef *hsai)
{
  /* Disable SAI peripheral */
  __HAL_SAI_DISABLE(hsai);

  HAL_SAI_DeInit(hsai);
}

/**
  * @}
  */

/** @defgroup STM32H745I_DISCOVERY_AUDIO_IN_Exported_Functions IN Exported Functions
  * @{
  */

/**
  * @brief  Initialize wave recording.
  * @param  AudioFreq: Audio frequency to be configured for the DFSDM peripheral.
  * @param  BitRes: Audio frequency to be configured for the DFSDM peripheral.
  * @param  ChnlNbr: Audio frequency to be configured for the DFSDM peripheral.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_Init(uint32_t AudioFreq, uint32_t BitRes, uint32_t ChnlNbr)
{
  /* Set audio in interface to default one */
  BSP_AUDIO_IN_SelectInterface(AUDIO_IN_INTERFACE_PDM);
  return  BSP_AUDIO_IN_InitEx(INPUT_DEVICE_DIGITAL_MIC, AudioFreq, BitRes, ChnlNbr);
}

/**
  * @brief  Initialize wave recording.
  * @param  InputDevice: INPUT_DEVICE_DIGITAL_MIC or INPUT_DEVICE_ANALOG_MIC.
  * @param  AudioFreq: Audio frequency to be configured.
  * @param  BitRes: Audio bit resolution to be configured..
  * @param  ChnlNbr: Number of channel to be configured.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_InitEx(uint16_t InputDevice, uint32_t AudioFreq, uint32_t BitRes, uint32_t ChnlNbr)
{
  uint8_t ret = AUDIO_OK;
  uint32_t slot_active;

  /* Store the audio record context */
  hAudioIn.Frequency     = AudioFreq;
  hAudioIn.BitResolution = BitRes;
  hAudioIn.InputDevice = InputDevice;
  hAudioIn.ChannelNbr = ChnlNbr;

  if(hAudioIn.InputDevice == INPUT_DEVICE_DIGITAL_MIC)
  {
    if(hAudioIn.Interface == AUDIO_IN_INTERFACE_SAI)
    {
      /* Initialize SAI2 block B as SLAVE RX synchrounous with SAI2 block A */
      haudio_in_sai.Instance = AUDIO_IN_SAIx;

      /* Disable SAI */
      SAIx_In_DeInit(&haudio_in_sai);

      /* PLL clock is set depending on the AudioFreq (44.1khz vs 48khz groups) */
      BSP_AUDIO_IN_ClockConfig(AudioFreq, NULL); /* Clock config is shared between AUDIO IN and OUT */

      /* SAI data transfer preparation:
      Prepare the Media to be used for the audio transfer from SAI peripheral to memory */
      if(HAL_SAI_GetState(&haudio_in_sai) == HAL_SAI_STATE_RESET)
      {
        /* Init the SAI MSP: this __weak function can be redefined by the application*/
        BSP_AUDIO_IN_MspInit();
      }

      /* Configure SAI in master mode :
       *   - SAI2_block_B in slave RX mode synchronous from SAI2_block_A
       */
      slot_active = CODEC_AUDIOFRAME_SLOT_13;
      SAIx_In_Init(SAI_MODESLAVE_RX, slot_active, AudioFreq);
    }
    else if(hAudioIn.Interface == AUDIO_IN_INTERFACE_PDM)
    {
      /* Initialize SAI2 block A as MASTER RX */
      haudio_in_sai.Instance = AUDIO_IN_SAI_PDMx;

      /* Disable SAI */
      SAIx_In_DeInit(&haudio_in_sai);

      /* PLL clock is set depending on the AudioFreq (44.1khz vs 48khz groups) */
      BSP_AUDIO_IN_ClockConfig(AudioFreq, NULL);

      /* SAI data transfer preparation:
      Prepare the Media to be used for the audio transfer from SAI peripheral to memory */
      /* Initialize the haudio_in_sai Instance parameter */

      if(HAL_SAI_GetState(&haudio_in_sai) == HAL_SAI_STATE_RESET)
      {
        /* Init the SAI MSP: this __weak function can be redefined by the application*/
        BSP_AUDIO_IN_MspInit();
      }

      /* Configure SAI in master mode :
       *   - SAI4_block_A in master RX mode
       */
      slot_active = CODEC_AUDIOFRAME_SLOT_1;
      SAIx_In_Init(SAI_MODEMASTER_RX, slot_active, AudioFreq);

      if(BSP_AUDIO_IN_PDMToPCM_Init(AudioFreq, hAudioIn.ChannelNbr, hAudioIn.ChannelNbr) != AUDIO_OK)
      {
        ret = AUDIO_ERROR;
      }
    }
    else
    {
      ret = AUDIO_ERROR;
    }
  }
  else
  {
    /* Analog Input */
    ret = AUDIO_ERROR;
  }

  /* Return AUDIO_OK when all operations are correctly done */
  return ret;
}

/**
  * @brief  Initializes wave recording and playback in parallel.
  * @param  InputDevice: INPUT_DEVICE_DIGITAL_MICROPHONE_2
  * @param  OutputDevice: OUTPUT_DEVICE_SPEAKER, OUTPUT_DEVICE_HEADPHONE,
  *                       or OUTPUT_DEVICE_BOTH.
  * @param  AudioFreq: Audio frequency to be configured for the SAI peripheral.
  * @param  BitRes: Audio frequency to be configured.
  * @param  ChnlNbr: Channel number.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_OUT_Init(uint32_t InputDevice, uint32_t OutputDevice, uint32_t AudioFreq, uint32_t BitRes, uint32_t ChnlNbr)
{
  uint32_t slot_active;
  uint32_t deviceid = 0, ret = AUDIO_OK;

  /* Store the audio record context */
  hAudioIn.Frequency     = AudioFreq;
  hAudioIn.BitResolution = BitRes;
  hAudioIn.InputDevice = InputDevice;
  hAudioIn.ChannelNbr = ChnlNbr;

  /* Input device is Digital MIC2 and Codec interface is SAI */
  if (hAudioIn.InputDevice == INPUT_DEVICE_DIGITAL_MICROPHONE_2)
  {
    haudio_in_sai.Instance = AUDIO_IN_SAIx;
    haudio_out_sai.Instance = AUDIO_OUT_SAIx;

    /* PLL clock is set depending on the AudioFreq (44.1khz vs 48khz groups) */
    BSP_AUDIO_OUT_ClockConfig(&haudio_in_sai, AudioFreq, NULL);
    /* SAI data transfer preparation:
    Prepare the Media to be used for the audio transfer from SAI peripheral to memory */
    if(HAL_SAI_GetState(&haudio_in_sai) == HAL_SAI_STATE_RESET)
    {
      /* Init the SAI MSP: this __weak function can be redefined by the application*/
      BSP_AUDIO_IN_MspInit();
    }

    /* SAI data transfer preparation:
    Prepare the Media to be used for the audio transfer from memory to SAI peripheral */
    if(HAL_SAI_GetState(&haudio_out_sai) == HAL_SAI_STATE_RESET)
    {
      /* Init the SAI MSP: this __weak function can be redefined by the application*/
      BSP_AUDIO_OUT_MspInit(&haudio_out_sai, NULL);
    }

    /* Configure SAI in master TX mode :
    *   - SAI2_block_A in master TX mode
    *   - SAI2_block_B in slave RX mode synchronous from SAI2_block_A
    */
    slot_active = CODEC_AUDIOFRAME_SLOT_13;
    SAIx_In_Init(SAI_MODESLAVE_RX, slot_active, AudioFreq);

    slot_active = CODEC_AUDIOFRAME_SLOT_02;
    SAIx_Out_Init(SAI_MODEMASTER_TX, slot_active, AudioFreq);

    /* wm8994 codec initialization */
    deviceid = wm8994_drv.ReadID(AUDIO_I2C_ADDRESS);

    if((deviceid) == WM8994_ID)
    {
      /* Reset the Codec Registers */
      wm8994_drv.Reset(AUDIO_I2C_ADDRESS);
      /* Initialize the audio driver structure */
      audio_drv = &wm8994_drv;
      ret = AUDIO_OK;
    }
    else
    {
      ret = AUDIO_ERROR;
    }

    if(ret == AUDIO_OK)
    {
      /* Initialize the codec internal registers */
      audio_drv->Init(AUDIO_I2C_ADDRESS, InputDevice|OutputDevice, 90, AudioFreq);
    }
  }
  else
  {
    ret = AUDIO_ERROR;
  }

  /* Return AUDIO_OK when all operations are correctly done */
  return ret;
}

/**
  * @brief  Link digital mic to specified source
  * @param  Interface : Audio In interface for Digital mic. It can be:
  *                       AUDIO_IN_INTERFACE_SAI
  *                       AUDIO_IN_INTERFACE_PDM
  * @retval None
  */
void BSP_AUDIO_IN_SelectInterface(uint32_t Interface)
{
  hAudioIn.Interface = Interface;
}

/**
  * @brief  Get digital mic interface
  * @retval Digital mic interface.
  */
uint32_t BSP_AUDIO_IN_GetInterface(void)
{
  return (hAudioIn.Interface);
}

/**
  * @brief  Return audio in channel number
  * @retval Number of channel
  */
uint8_t BSP_AUDIO_IN_GetChannelNumber(void)
{
  return hAudioIn.ChannelNbr;
}

/**
  * @brief  Start audio recording.
  * @param  pBuf: Main buffer pointer for the recorded data storing
  * @param  size: Current size of the recorded buffer
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_Record(uint16_t *pBuf, uint32_t size)
{
  /* Start the process receive DMA */
  if(HAL_OK != HAL_SAI_Receive_DMA(&haudio_in_sai, (uint8_t*)pBuf, size))
  {
    return AUDIO_ERROR;
  }

  /* Return AUDIO_OK when all operations are correctly done */
  return AUDIO_OK;
}

/**
  * @brief  Stop audio recording.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_Stop(void)
{
  /* Call the Media layer stop function */
  HAL_SAI_DMAStop(&haudio_in_sai);

  /* Return AUDIO_OK when all operations are correctly done */
  return AUDIO_OK;
}

/**
  * @brief  Pause the audio file stream.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_Pause(void)
{
  if (hAudioIn.InputDevice == INPUT_DEVICE_ANALOG_MIC)
  {
    return AUDIO_ERROR;
  }
  else
  {
     /* Call the Media layer pause function */
    HAL_SAI_DMAPause(&haudio_in_sai);
  }

  /* Return AUDIO_OK when all operations are correctly done */
  return AUDIO_OK;
}

/**
  * @brief  Resume the audio file stream.
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_Resume(void)
{
  if (hAudioIn.InputDevice == INPUT_DEVICE_ANALOG_MIC)
  {
    return AUDIO_ERROR;
  }
  else
  {
     /* Call the Media layer resume function */
    HAL_SAI_DMAResume(&haudio_in_sai);
  }

  /* Return AUDIO_OK when all operations are correctly done */
  return AUDIO_OK;
}

/**
  * @brief  Controls the audio in volume level.
  * @param  Volume: Volume level to be set in percentage from 0% to 100% (0 for
  *         Mute and 100 for Max volume level).
  * @retval AUDIO_OK if correct communication, else wrong communication
  */
uint8_t BSP_AUDIO_IN_SetVolume(uint8_t Volume)
{
  /* Set the Global variable AudioInVolume  */
  AudioInVolume = Volume;

  /* Return AUDIO_OK when all operations are correctly done */
  return AUDIO_OK;
}

/**
  * @brief  Deinit the audio IN peripherals.
  * @retval None
  */
void BSP_AUDIO_IN_DeInit(void)
{
  SAIx_In_DeInit(&haudio_in_sai);

  BSP_AUDIO_IN_MspDeInit();
}

/**
* @brief  Initialize the PDM library.
* @param  AudioFreq: Audio sampling frequency
* @param  ChnlNbrIn: Number of input audio channels in the PDM buffer
* @param  ChnlNbrOut: Number of desired output audio channels in the  resulting PCM buffer
* @retval None
*/
uint8_t BSP_AUDIO_IN_PDMToPCM_Init(uint32_t AudioFreq, uint32_t ChnlNbrIn, uint32_t ChnlNbrOut)
{
  uint32_t index = 0;

  /* Enable CRC peripheral to unlock the PDM library */
  __HAL_RCC_CRC_CLK_ENABLE();

  for(index = 0; index < ChnlNbrIn; index++)
  {
    /* Init PDM filters */
    PDM_FilterHandler[index].bit_order  = PDM_FILTER_BIT_ORDER_MSB;
    PDM_FilterHandler[index].endianness = PDM_FILTER_ENDIANNESS_LE;
    PDM_FilterHandler[index].high_pass_tap = 2122358088;
    PDM_FilterHandler[index].out_ptr_channels = ChnlNbrOut;
    PDM_FilterHandler[index].in_ptr_channels  = ChnlNbrIn;
    PDM_Filter_Init((PDM_Filter_Handler_t *)(&PDM_FilterHandler[index]));

    /* PDM lib config phase */
    PDM_FilterConfig[index].output_samples_number = AudioFreq/1000;
    PDM_FilterConfig[index].mic_gain = 24;
    PDM_FilterConfig[index].decimation_factor = PDM_FILTER_DEC_FACTOR_64;
    PDM_Filter_setConfig((PDM_Filter_Handler_t *)&PDM_FilterHandler[index], &PDM_FilterConfig[index]);
  }

  return AUDIO_OK;
}


/**
  * @brief  Converts audio format from PDM to PCM.
  * @param  PDMBuf: Pointer to PDM buffer data
  * @param  PCMBuf: Pointer to PCM buffer data
  * @retval AUDIO_OK in case of success, AUDIO_ERROR otherwise
  */
uint8_t BSP_AUDIO_IN_PDMToPCM(uint16_t *PDMBuf, uint16_t *PCMBuf)
{
  uint32_t index = 0;

  for(index = 0; index < hAudioIn.ChannelNbr; index++)
  {
    PDM_Filter(&((uint8_t*)(PDMBuf))[index], (uint16_t*)&(PCMBuf[index]), &PDM_FilterHandler[index]);
  }

  return AUDIO_OK;
}

/**
  * @brief  User callback when record buffer is filled.
  * @retval None
  */
__weak void BSP_AUDIO_IN_TransferComplete_CallBack(void)
{
  /* This function should be implemented by the user application.
     It is called into this driver when the current buffer is filled
     to prepare the next buffer pointer and its size. */
}

/**
  * @brief  Manages the DMA Half Transfer complete event.
  * @retval None
  */
__weak void BSP_AUDIO_IN_HalfTransfer_CallBack(void)
{
  /* This function should be implemented by the user application.
     It is called into this driver when the current buffer is filled
     to prepare the next buffer pointer and its size. */
}

/**
  * @brief  User callback when record buffer is filled.
  * @param  InputDevice: INPUT_DEVICE_DIGITAL_MIC1 or INPUT_DEVICE_DIGITAL_MIC2
  */
__weak void BSP_AUDIO_IN_TransferComplete_CallBackEx(uint32_t InputDevice)
{
  /* This function should be implemented by the user application.
     It is called into this driver when the current buffer is filled
     to prepare the next buffer pointer and its size. */
}

/**
  * @brief  User callback when record buffer is filled.
  * @param InputDevice: INPUT_DEVICE_DIGITAL_MIC1 or INPUT_DEVICE_DIGITAL_MIC2
  */
__weak void BSP_AUDIO_IN_HalfTransfer_CallBackEx(uint32_t InputDevice)
{
  /* This function should be implemented by the user application.
     It is called into this driver when the current buffer is filled
     to prepare the next buffer pointer and its size. */
}

/**
  * @brief  Audio IN Error callback function.
  * @retval None
  */
__weak void BSP_AUDIO_IN_Error_CallBack(void)
{
  /* This function is called when an Interrupt due to transfer error on or peripheral
     error occurs. */
}

/**
  * @brief  Initialize BSP_AUDIO_IN MSP.
  * @retval None
  */
__weak void BSP_AUDIO_IN_MspInit(void)
{
  SAIx_In_MspInit(&haudio_in_sai, NULL);
}

/**
  * @brief  DeInitialize BSP_AUDIO_IN MSP.
  * @retval None
  */
__weak void BSP_AUDIO_IN_MspDeInit(void)
{
  SAIx_In_MspDeInit(&haudio_in_sai, NULL);
}

/**
  * @brief  Clock Config.
  * @param  AudioFreq: Audio frequency used to play the audio stream.
  * @param  Params: pointer on additional configuration parameters, can be NULL.
  * @note   This API is called by BSP_AUDIO_IN_Init()
  *         Being __weak it can be overwritten by the application
  * @retval None
  */
__weak void BSP_AUDIO_IN_ClockConfig(uint32_t AudioFreq, void *Params)
{
  RCC_PeriphCLKInitTypeDef rcc_ex_clk_init_struct;

  HAL_RCCEx_GetPeriphCLKConfig(&rcc_ex_clk_init_struct);

  /* Set the PLL configuration according to the audio frequency */
  if((AudioFreq == AUDIO_FREQUENCY_11K) || (AudioFreq == AUDIO_FREQUENCY_22K) || (AudioFreq == AUDIO_FREQUENCY_44K))
  {
    /* SAI clock config:
       PLL2_VCO Input = HSE_VALUE/PLL2M = 1 Mhz
       PLL2_VCO Output = PLL2_VCO Input * PLL2N = 429 Mhz
       SAI_CLK_x = PLL2_VCO Output/PLL2P = 429/38 = 11.289 Mhz */
    rcc_ex_clk_init_struct.PeriphClockSelection = RCC_PERIPHCLK_SAI2;
    rcc_ex_clk_init_struct.Sai23ClockSelection = RCC_SAI2CLKSOURCE_PLL2;
    rcc_ex_clk_init_struct.PLL2.PLL2P = 38;
    rcc_ex_clk_init_struct.PLL2.PLL2Q = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2R = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2N = 429;
    rcc_ex_clk_init_struct.PLL2.PLL2M = 25;
    if (hAudioIn.Interface == AUDIO_IN_INTERFACE_PDM)
    {
      rcc_ex_clk_init_struct.PeriphClockSelection = RCC_PERIPHCLK_SAI4A;
      rcc_ex_clk_init_struct.Sai4AClockSelection = RCC_SAI4ACLKSOURCE_PLL2;
    }
    HAL_RCCEx_PeriphCLKConfig(&rcc_ex_clk_init_struct);

  }
  else /* AUDIO_FREQUENCY_8K, AUDIO_FREQUENCY_16K, AUDIO_FREQUENCY_32K, AUDIO_FREQUENCY_48K, AUDIO_FREQUENCY_96K */
  {
    /* SAI clock config:
       PLL2_VCO Input = HSE_VALUE/PLL2M = 1 Mhz
       PLL2_VCO Output = PLL2_VCO Input * PLL2N = 344 Mhz
       SAI_CLK_x = PLL2_VCO Output/PLL2P = 344/7 = 49.142 Mhz */
    rcc_ex_clk_init_struct.PeriphClockSelection = RCC_PERIPHCLK_SAI2;
    rcc_ex_clk_init_struct.Sai23ClockSelection = RCC_SAI2CLKSOURCE_PLL2;
    rcc_ex_clk_init_struct.PLL2.PLL2P = 7;
    rcc_ex_clk_init_struct.PLL2.PLL2Q = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2R = 1;
    rcc_ex_clk_init_struct.PLL2.PLL2N = 344;
    rcc_ex_clk_init_struct.PLL2.PLL2M = 25;
    if (hAudioIn.Interface == AUDIO_IN_INTERFACE_PDM)
    {
      rcc_ex_clk_init_struct.PeriphClockSelection = RCC_PERIPHCLK_SAI4A;
      rcc_ex_clk_init_struct.Sai4AClockSelection = RCC_SAI4ACLKSOURCE_PLL2;
    }
    HAL_RCCEx_PeriphCLKConfig(&rcc_ex_clk_init_struct);
  }
}
/**
  * @}
  */


/** @defgroup STM32H745I_DISCOVERY_AUDIO_IN_Private_Functions IN Private Functions
  * @{
  */

/*******************************************************************************
                            HAL Callbacks
*******************************************************************************/

/**
  * @brief  Half reception complete callback.
  * @param  hsai: SAI handle.
  * @retval None
  */
void HAL_SAI_RxHalfCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* Manage the remaining file size and new address offset: This function should be coded by user */
  BSP_AUDIO_IN_HalfTransfer_CallBack();
}

/**
  * @brief  Reception complete callback.
  * @param  hsai: SAI handle.
  * @retval None
  */
void HAL_SAI_RxCpltCallback(SAI_HandleTypeDef *hsai)
{
  /* Call the record update function to get the next buffer to fill and its size (size is ignored) */
  BSP_AUDIO_IN_TransferComplete_CallBack();
}

/*******************************************************************************
                            Static Functions
*******************************************************************************/
/**
  * @brief  Initializes SAI Audio IN MSP.
  * @param  hsai: SAI handle
  * @param  Params: pointer on additional configuration parameters, can be NULL.
  * @retval None
  */
static void SAIx_In_MspInit(SAI_HandleTypeDef *hsai, void *Params)
{
  static DMA_HandleTypeDef hdma_sai_rx;
  GPIO_InitTypeDef  gpio_init_structure;

  if(hsai->Instance == AUDIO_IN_SAI_PDMx)
  {
    /* Enable SAI clock */
    AUDIO_IN_SAI_PDMx_CLK_ENABLE();

    /* Enable PDM clock */
    AUDIO_IN_SAI_PDMx_CLK_IN_ENABLE();
    gpio_init_structure.Pin = AUDIO_IN_SAI_PDMx_CLK_IN_PIN;
    gpio_init_structure.Mode = GPIO_MODE_AF_PP;
    gpio_init_structure.Pull = GPIO_NOPULL;
    gpio_init_structure.Speed = GPIO_SPEED_FREQ_HIGH;
    gpio_init_structure.Alternate = AUDIO_IN_SAI_PDMx_DATA_CLK_AF;
    HAL_GPIO_Init(AUDIO_IN_SAI_PDMx_CLK_IN_PORT, &gpio_init_structure);

    /* Enable PDM data */
    AUDIO_IN_SAI_PDMx_DATA_IN_ENABLE();
    gpio_init_structure.Pull = GPIO_PULLUP;
    gpio_init_structure.Speed = GPIO_SPEED_FREQ_MEDIUM;
    gpio_init_structure.Pin = AUDIO_IN_SAI_PDMx_DATA_IN_PIN;
    HAL_GPIO_Init(AUDIO_IN_SAI_PDMx_DATA_IN_PORT, &gpio_init_structure);

    /* Enable the DMA clock */
    AUDIO_IN_SAI_PDMx_DMAx_CLK_ENABLE();

    /* Configure the hdma_sai_rx handle parameters */
    hdma_sai_rx.Init.Request             = AUDIO_IN_SAI_PDMx_DMAx_REQUEST;
    hdma_sai_rx.Init.Direction           = DMA_PERIPH_TO_MEMORY;
    hdma_sai_rx.Init.PeriphInc           = DMA_PINC_DISABLE;
    hdma_sai_rx.Init.MemInc              = DMA_MINC_ENABLE;
    hdma_sai_rx.Init.PeriphDataAlignment = AUDIO_IN_SAI_PDMx_DMAx_PERIPH_DATA_SIZE;
    hdma_sai_rx.Init.MemDataAlignment    = AUDIO_IN_SAI_PDMx_DMAx_MEM_DATA_SIZE;
    hdma_sai_rx.Init.Mode                = DMA_CIRCULAR;
    hdma_sai_rx.Init.Priority            = DMA_PRIORITY_HIGH;
    hdma_sai_rx.Init.FIFOMode            = DMA_FIFOMODE_DISABLE;
    hdma_sai_rx.Init.FIFOThreshold       = DMA_FIFO_THRESHOLD_FULL;
    hdma_sai_rx.Init.MemBurst            = DMA_MBURST_SINGLE;
    hdma_sai_rx.Init.PeriphBurst         = DMA_MBURST_SINGLE;

    hdma_sai_rx.Instance = AUDIO_IN_SAI_PDMx_DMAx_STREAM;

    /* Associate the DMA handle */
    __HAL_LINKDMA(hsai, hdmarx, hdma_sai_rx);

    /* Deinitialize the Stream for new transfer */
    HAL_DMA_DeInit(&hdma_sai_rx);

    /* Configure the DMA Stream */
    HAL_DMA_Init(&hdma_sai_rx);

    /* SAI DMA IRQ Channel configuration */
    HAL_NVIC_SetPriority(AUDIO_IN_SAI_PDMx_DMAx_IRQ, AUDIO_IN_IRQ_PREPRIO, 0);
    HAL_NVIC_EnableIRQ(AUDIO_IN_SAI_PDMx_DMAx_IRQ);
  }
  else
  {
    /* Enable SAI clock */
    AUDIO_IN_SAIx_CLK_ENABLE();

    /* Enable SD GPIO clock */
    AUDIO_IN_SAIx_SD_ENABLE();
    /* CODEC_SAI pin configuration: SD pin */
    gpio_init_structure.Pin = AUDIO_IN_SAIx_SD_PIN;
    gpio_init_structure.Mode = GPIO_MODE_AF_PP;
    gpio_init_structure.Pull = GPIO_NOPULL;
    gpio_init_structure.Speed = GPIO_SPEED_FREQ_HIGH;
    gpio_init_structure.Alternate = AUDIO_IN_SAIx_AF;
    HAL_GPIO_Init(AUDIO_IN_SAIx_SD_GPIO_PORT, &gpio_init_structure);

    /* Enable the DMA clock */
    AUDIO_IN_SAIx_DMAx_CLK_ENABLE();

    /* Configure the hdma_sai_rx handle parameters */
    hdma_sai_rx.Init.Request             = AUDIO_IN_SAIx_DMAx_REQUEST;
    hdma_sai_rx.Init.Direction           = DMA_PERIPH_TO_MEMORY;
    hdma_sai_rx.Init.PeriphInc           = DMA_PINC_DISABLE;
    hdma_sai_rx.Init.MemInc              = DMA_MINC_ENABLE;
    hdma_sai_rx.Init.PeriphDataAlignment = AUDIO_IN_SAIx_DMAx_PERIPH_DATA_SIZE;
    hdma_sai_rx.Init.MemDataAlignment    = AUDIO_IN_SAIx_DMAx_MEM_DATA_SIZE;
    hdma_sai_rx.Init.Mode                = DMA_CIRCULAR;
    hdma_sai_rx.Init.Priority            = DMA_PRIORITY_HIGH;
    hdma_sai_rx.Init.FIFOMode            = DMA_FIFOMODE_DISABLE;
    hdma_sai_rx.Init.FIFOThreshold       = DMA_FIFO_THRESHOLD_FULL;
    hdma_sai_rx.Init.MemBurst            = DMA_MBURST_SINGLE;
    hdma_sai_rx.Init.PeriphBurst         = DMA_MBURST_SINGLE;

    hdma_sai_rx.Instance = AUDIO_IN_SAIx_DMAx_STREAM;

    /* Associate the DMA handle */
    __HAL_LINKDMA(hsai, hdmarx, hdma_sai_rx);

    /* Deinitialize the Stream for new transfer */
    HAL_DMA_DeInit(&hdma_sai_rx);

    /* Configure the DMA Stream */
    HAL_DMA_Init(&hdma_sai_rx);

    /* SAI DMA IRQ Channel configuration */
    HAL_NVIC_SetPriority(AUDIO_IN_SAIx_DMAx_IRQ, AUDIO_IN_IRQ_PREPRIO, 0);
    HAL_NVIC_EnableIRQ(AUDIO_IN_SAIx_DMAx_IRQ);
  }
}

/**
  * @brief  De-Initializes SAI Audio IN MSP.
  * @param  hsai: SAI handle
  * @param  Params: pointer on additional configuration parameters, can be NULL.
  * @retval None
  */
static void SAIx_In_MspDeInit(SAI_HandleTypeDef *hsai, void *Params)
{
  GPIO_InitTypeDef  gpio_init_structure;

  if(hsai->Instance == AUDIO_IN_SAI_PDMx)
  {
    /* Deinitialize the DMA stream */
    HAL_DMA_Abort(hsai->hdmarx);

    HAL_SAI_DeInit(hsai);
    /* Disable SAI peripheral */
    __HAL_SAI_DISABLE(hsai);

    /* Deinitialize the DMA stream */
    HAL_DMA_DeInit(hsai->hdmarx);

    gpio_init_structure.Pin = AUDIO_IN_SAI_PDMx_CLK_IN_PIN;
    HAL_GPIO_DeInit(AUDIO_IN_SAI_PDMx_CLK_IN_PORT, gpio_init_structure.Pin);

    gpio_init_structure.Pin = AUDIO_IN_SAI_PDMx_DATA_IN_PIN;
    HAL_GPIO_DeInit(AUDIO_IN_SAI_PDMx_DATA_IN_PORT, gpio_init_structure.Pin);

    /* Disable SAI clock */
    AUDIO_IN_SAI_PDMx_CLK_DISABLE();
  }
  else
  {
    /* SAI DMA IRQ Channel deactivation */
    HAL_NVIC_DisableIRQ(AUDIO_IN_SAIx_DMAx_IRQ);

    if(hsai->Instance == AUDIO_IN_SAIx)
    {
      /* Deinitialize the DMA stream */
      HAL_DMA_DeInit(hsai->hdmatx);
    }

    /* Disable SAI peripheral */
    __HAL_SAI_DISABLE(hsai);

    /* Deactivates CODEC_SAI pin SD by putting them in input mode */
    gpio_init_structure.Pin = AUDIO_IN_SAIx_SD_PIN;
    HAL_GPIO_DeInit(AUDIO_IN_SAIx_SD_GPIO_PORT, gpio_init_structure.Pin);

    /* Disable SAI clock */
    AUDIO_IN_SAIx_CLK_DISABLE();
  }
}

/**
  * @brief  Initializes the Audio Codec audio interface (SAI).
  * @param  SaiInMode: Audio mode to be configured for the SAI peripheral.
  * @param  SlotActive: Audio active slot to be configured for the SAI peripheral.
  * @param  AudioFreq: Audio frequency to be configured for the SAI peripheral.
  * @retval None
  */
static void SAIx_In_Init(uint32_t SaiInMode, uint32_t SlotActive, uint32_t AudioFreq)
{
  /* Disable SAI peripheral to allow access to SAI internal registers */
  __HAL_SAI_DISABLE(&haudio_in_sai);

  /* Configure SAI_Block_x
  LSBFirst: Disabled
  DataSize: 16 */
  haudio_in_sai.Init.MonoStereoMode = SAI_STEREOMODE;
  haudio_in_sai.Init.AudioFrequency = AudioFreq;
  haudio_in_sai.Init.AudioMode      = SaiInMode;
  haudio_in_sai.Init.NoDivider      = SAI_MASTERDIVIDER_ENABLE;
  haudio_in_sai.Init.Protocol       = SAI_FREE_PROTOCOL;
  haudio_in_sai.Init.DataSize       = SAI_DATASIZE_16;
  haudio_in_sai.Init.FirstBit       = SAI_FIRSTBIT_MSB;
  haudio_in_sai.Init.ClockStrobing  = SAI_CLOCKSTROBING_RISINGEDGE;
  haudio_in_sai.Init.Synchro        = SAI_SYNCHRONOUS;
  haudio_in_sai.Init.OutputDrive    = SAI_OUTPUTDRIVE_DISABLE;
  haudio_in_sai.Init.FIFOThreshold  = SAI_FIFOTHRESHOLD_1QF;
  haudio_in_sai.Init.SynchroExt     = SAI_SYNCEXT_DISABLE;
  haudio_in_sai.Init.CompandingMode = SAI_NOCOMPANDING;
  haudio_in_sai.Init.TriState       = SAI_OUTPUT_RELEASED;
  haudio_in_sai.Init.Mckdiv         = 0;
  haudio_in_sai.Init.MckOverSampling = SAI_MCK_OVERSAMPLING_DISABLE;
  haudio_in_sai.Init.PdmInit.Activation  = DISABLE;

  /* Configure SAI_Block_x Frame
  Frame Length: 64
  Frame active Length: 32
  FS Definition: Start frame + Channel Side identification
  FS Polarity: FS active Low
  FS Offset: FS asserted one bit before the first bit of slot 0 */
  haudio_in_sai.FrameInit.FrameLength       = 128;
  haudio_in_sai.FrameInit.ActiveFrameLength = 64;
  haudio_in_sai.FrameInit.FSDefinition      = SAI_FS_CHANNEL_IDENTIFICATION;
  haudio_in_sai.FrameInit.FSPolarity        = SAI_FS_ACTIVE_LOW;
  haudio_in_sai.FrameInit.FSOffset          = SAI_FS_BEFOREFIRSTBIT;

  /* Configure SAI Block_x Slot
  Slot First Bit Offset: 0
  Slot Size  : 16
  Slot Number: 4
  Slot Active: All slot active */
  haudio_in_sai.SlotInit.FirstBitOffset = 0;
  haudio_in_sai.SlotInit.SlotSize       = SAI_SLOTSIZE_DATASIZE;
  haudio_in_sai.SlotInit.SlotNumber     = 4;
  haudio_in_sai.SlotInit.SlotActive     = SlotActive;

  if(hAudioIn.Interface == AUDIO_IN_INTERFACE_PDM)
  {
    haudio_in_sai.Init.AudioFrequency      = AudioFreq * 8;
    haudio_in_sai.Init.Synchro             = SAI_ASYNCHRONOUS;
    haudio_in_sai.Init.NoDivider           = SAI_MASTERDIVIDER_DISABLE;

    haudio_in_sai.Init.PdmInit.Activation  = ENABLE;
    haudio_in_sai.Init.PdmInit.MicPairsNbr = 2;
    haudio_in_sai.Init.PdmInit.ClockEnable = SAI_PDM_CLOCK2_ENABLE;
    haudio_in_sai.Init.FirstBit            = SAI_FIRSTBIT_LSB;
    haudio_in_sai.Init.ClockStrobing       = SAI_CLOCKSTROBING_FALLINGEDGE;

    haudio_in_sai.FrameInit.FrameLength       = 32;
    haudio_in_sai.FrameInit.ActiveFrameLength = 1;
    haudio_in_sai.FrameInit.FSDefinition      = SAI_FS_STARTFRAME;
    haudio_in_sai.FrameInit.FSPolarity        = SAI_FS_ACTIVE_HIGH;
    haudio_in_sai.FrameInit.FSOffset          = SAI_FS_FIRSTBIT;

    haudio_in_sai.SlotInit.SlotNumber     = 2;
    haudio_in_sai.SlotInit.SlotActive     = SlotActive;
  }

  HAL_SAI_Init(&haudio_in_sai);

  /* Enable SAI peripheral */
  __HAL_SAI_ENABLE(&haudio_in_sai);
}

/**
  * @brief  Deinitializes the output Audio Codec audio interface (SAI).
  * @retval None
  */
static void SAIx_In_DeInit(SAI_HandleTypeDef *hsai)
{
  /* Disable SAI peripheral */
  __HAL_SAI_DISABLE(hsai);

  HAL_SAI_DeInit(hsai);
}

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
