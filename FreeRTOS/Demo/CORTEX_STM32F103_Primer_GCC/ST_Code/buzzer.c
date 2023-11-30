/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     buzzer.c
* @brief    Buzzer dedicated functions with RTTTL format support.
* @author   IB
* @date     07/2007
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "circle.h"

/// @cond Internal

/* Private typedef -----------------------------------------------------------*/

/*! Octaves */
enum eOctave  {
      OCT_440  = 0,  /*!< o = 5 */
      OCT_880  = 1,  /*!< o = 6 */
      OCT_1760 = 2,  /*!< o = 7 */
      OCT_3520 = 3,  /*!< o = 8 */
      OCT_7040 = 4   /*!< o = 9 */
      } octave;

/*! Notes */
enum eNotes  {
      NOTE_PAUSE = 0,    /*!< P  */
      NOTE_LA    = 1,    /*!< A  */
      NOTE_LA_H  = 8+1,  /*!< A# */
      NOTE_SI    = 2,    /*!< B  */
      NOTE_DO    = 3,    /*!< C  */
      NOTE_DO_H  = 8+3,  /*!< C# */
      NOTE_RE    = 4,    /*!< D  */
      NOTE_RE_H  = 8+4,  /*!< D# */
      NOTE_MI    = 5,    /*!< E  */
      NOTE_FA    = 6,    /*!< F  */
      NOTE_FA_H  = 8+6,  /*!< F# */
      NOTE_SOL   = 7,    /*!< G  */
      NOTE_SOL_H = 8+7   /*!< G# */
      } note;

/* Private define ------------------------------------------------------------*/
#define BUZZER_SHORTBEEP_DURATION   100
#define BUZZER_LONGBEEP_DURATION    1000
#define RTTTL_SEP                   ':'
   
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
int                              buzz_counter         = 0;
int                              buzz_in_progress     = 0;
static TIM_TimeBaseInitTypeDef   TIM_TimeBaseStructure;
static TIM_OCInitTypeDef         TIM_OCInitStructure;
u16                              CCR_Val              = 0x2EE0;
enum BUZZER_mode                 Buzzer_Mode          = BUZZER_UNDEF;
u32                              Buzzer_Counter       = 0;

// For the melody.
const u8*                        CurrentMelody        = 0;
const u8*                        CurrentMelodySTART   = 0;
u8                               DefaultOctave        = OCT_880;
u8                               DefaultDuration      = 4;
u16                              DefaultBeats         = 63;

u16 Note_Freq [16] = {
   0,    //pause
   440,  //A=LA
   494,  //B=SI
   524,  //C=DO
   588,  //D=RE
   660,  //E=MI
   698,  //F=FA
   784,  //G=SOL
   0,    // "8+n" for "NOTE#"
   466,  //A#=LA#
   0,
   544,  //C#=DO#
   622,  //D#=RE#
   0,
   740,  //F#=FA#
   830   //G#=SOL#
   };

/* Private function prototypes -----------------------------------------------*/
static void PlayMusic( void );
static void BUZZER_SetFrequency( u16 freq );

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
*
*                                PlayMusic
*
*******************************************************************************/
/**
*
*  Play the next note of the current melody.
*
**/
/******************************************************************************/
static void PlayMusic( void )
   {
   u8 duration = DefaultDuration;
   u8 c;

   // Discard blank characters
   while ( *CurrentMelody == ' ')
      {
      CurrentMelody++;
      }

   // Check whether a duration is present.
   if ( (*CurrentMelody > '0') && (*CurrentMelody < '9') )
      {
      duration = *CurrentMelody++ - '0';

      if ( (*CurrentMelody > '0') && (*CurrentMelody < '9') )
         {
         duration *= 10;
         duration += (*CurrentMelody++ - '0');
         }
      }

   Buzzer_Counter = ( (32/duration) * 256L * 32L) / DefaultBeats;
   Buzzer_Counter*= (RCC_ClockFreq.SYSCLK_Frequency / 12000000L); //Adapt to HCLK1

   //read the note
   c = *CurrentMelody++;

   if ( (c >= 'a') && (c <= 'z') )
      {
      c+=('A'-'a');
      }

   if ( c == 'P' )
      {
      note = NOTE_PAUSE;
      }
   else if ( (c >= 'A') && (c <= 'G') )
      {
      note = (c - 'A') + NOTE_LA;

      if ( *CurrentMelody == '#' )
         {
         note|=0x8;
         CurrentMelody++;
         }
      }

   octave = DefaultOctave;
   c = *CurrentMelody;

   if ( (c>= '5') && (c<= '8') )
      {
      octave = OCT_440 + (c-'5');
      CurrentMelody++;
      }

   BUZZER_SetFrequency ( (Note_Freq [ note ] * (1<<octave)));

   //discard delimiter and ignore special duration
   while ( (c = *CurrentMelody++) != 0 )
      {
      if ( c==',')
         break;
      }

   if ( *(CurrentMelody-1)==0 )
      {
      CurrentMelody  = 0;
      }

   if ( c == 0 )
      {
      BUZZER_SetMode ( BUZZER_OFF );
      }
   }

/***********************************************************************************
*
*                                BUZZER_SetFrequency
*
************************************************************************************/
/**
*
*  Set the buzzer frequency
*
*  @param[in]  freq New frequency.
*
**/
/********************************************************************************/
void BUZZER_SetFrequency ( u16 freq )
   {
   /* Calculate the frequency (depend on the PCLK1 clock value) */
   CCR_Val = (RCC_ClockFreq.PCLK1_Frequency / freq);

   TIM_TimeBaseStructure.TIM_Period          = CCR_Val * 2;
   TIM_TimeBaseStructure.TIM_Prescaler       = 0x0;
   TIM_TimeBaseStructure.TIM_ClockDivision   = 0x0;
   TIM_TimeBaseStructure.TIM_CounterMode     = TIM_CounterMode_Up;

   TIM_TimeBaseInit( TIM3, &TIM_TimeBaseStructure );

   /* Output Compare Toggle Mode configuration: Channel3 */
   TIM_OCInitStructure.TIM_OCMode   = TIM_OCMode_PWM1;
   TIM_OCInitStructure.TIM_OutputState = TIM_OutputState_Enable;
   TIM_OCInitStructure.TIM_Pulse    = CCR_Val;

   TIM_OC3Init( TIM3, &TIM_OCInitStructure );
   TIM_OC3PreloadConfig( TIM3, TIM_OCPreload_Enable );
   }

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                                BUZZER_Init
*
*******************************************************************************/
/**
*
*  Buzzer Initialization
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void BUZZER_Init( void )
   {
   GPIO_InitTypeDef GPIO_InitStructure;

   /* Enable GPIOB clock  */
   RCC_APB2PeriphClockCmd( RCC_APB2Periph_GPIOB, ENABLE );

   /* GPIOB Configuration: TIM3 3in Output */
   GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_0;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_AF_PP;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;

   GPIO_Init( GPIOB, &GPIO_InitStructure );

   /* TIM3 Configuration ------------------------------------------------------*/
   /* TIM3CLK = 18 MHz, Prescaler = 0x0, TIM3 counter clock = 18  MHz */
   /* CC update rate = TIM3 counter clock / (2* CCR_Val) ~= 750 Hz */

   /* Enable TIM3 clock */
   RCC_APB1PeriphClockCmd( RCC_APB1Periph_TIM3, ENABLE );
   TIM_DeInit( TIM3 );
   TIM_TimeBaseStructInit( &TIM_TimeBaseStructure );
   TIM_OCStructInit( &TIM_OCInitStructure );

   /* Time base configuration */
   TIM_TimeBaseStructure.TIM_Period          = 0xFFFF;
   TIM_TimeBaseStructure.TIM_Prescaler       = 0x0;
   TIM_TimeBaseStructure.TIM_ClockDivision   = 0x0;
   TIM_TimeBaseStructure.TIM_CounterMode     = TIM_CounterMode_Up;

   TIM_TimeBaseInit( TIM3, &TIM_TimeBaseStructure );

   /* Output Compare Toggle Mode configuration: Channel3 */
   TIM_OCInitStructure.TIM_OCMode   = TIM_OCMode_Toggle;
   TIM_OCInitStructure.TIM_OutputState = TIM_OutputState_Enable;
   TIM_OCInitStructure.TIM_Pulse    = CCR_Val;

   TIM_OC3Init( TIM3, &TIM_OCInitStructure );
   TIM_OC3PreloadConfig( TIM3, TIM_OCPreload_Disable );
   BUZZER_SetFrequency( 440 );

   /* Enable TIM3 IT */
   TIM_ITConfig( TIM3, TIM_IT_CC3, ENABLE );

   Buzzer_Mode  = BUZZER_OFF;
   }

/*******************************************************************************
*
*                                BUZZER_Handler
*
*******************************************************************************/
/**
*
*  Called by the CircleOS scheduler to manage Buzzer tasks.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void BUZZER_Handler( void )
   {
   int fSetOFF = 0;

   if ( Buzzer_Mode == BUZZER_PLAYMUSIC )
      {
      if ( Buzzer_Counter == 0 )
         {
         PlayMusic();
         }
      else 
         {
         Buzzer_Counter--;
         }

      return;
      }
   else if ( Buzzer_Mode == BUZZER_SHORTBEEP )
      {
      if ( Buzzer_Counter++ == (BUZZER_SHORTBEEP_DURATION) ) 
         {
         Buzzer_Mode  = BUZZER_OFF;

         return;
         }
      if ( Buzzer_Counter == (BUZZER_SHORTBEEP_DURATION/2) )
         {
         fSetOFF = 1;
         }
      }
   else if ( Buzzer_Mode == BUZZER_LONGBEEP )
      {
      if ( Buzzer_Counter++ == (BUZZER_LONGBEEP_DURATION) )
         {
         Buzzer_Mode  = BUZZER_OFF;

         return;
         }
      if ( Buzzer_Counter > (BUZZER_LONGBEEP_DURATION/2) )
         {
         fSetOFF = 1;
         }
      }

   if ( fSetOFF == 1 )
      {
      TIM_Cmd(TIM3, DISABLE);
      }
   }

/// @endcond

/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                                BUZZER_GetMode
*
*******************************************************************************/
/**
*
*  Get the current buzzer mode.
*
*  @return  Current buzzer mode.
*
**/
/******************************************************************************/
enum BUZZER_mode BUZZER_GetMode( void )
   {
   return Buzzer_Mode;
   }

/*******************************************************************************
*
*                                BUZZER_SetMode
*
*******************************************************************************/
/**
*
*  Set new buzzer mode
*
*  @param[in]  mode  New buzzer mode.
*
**/
/******************************************************************************/
void BUZZER_SetMode( enum BUZZER_mode mode )
   {
   Buzzer_Mode    = mode;
   Buzzer_Counter = 0;

   switch ( mode )
      {
      case BUZZER_PLAYMUSIC   :
         PlayMusic(); //start melody
         /* no break */

      case BUZZER_LONGBEEP    :
      case BUZZER_SHORTBEEP   :
      case BUZZER_ON          :
         TIM_Cmd( TIM3, ENABLE );
         break;

      case BUZZER_OFF         :
         TIM_Cmd( TIM3, DISABLE );
         break;
      }
   }

/*******************************************************************************
*
*                                BUZZER_PlayMusic
*
*******************************************************************************/
/**
*
*  Plays the provided melody that follows the RTTTL Format.
*
*  Official Specification
*  @verbatim
<ringing-tones-text-transfer-language> :=
   <name> <sep> [<defaults>] <sep> <note-command>+
<name> := <char>+ ; maximum name length 10 characters
<sep> := ":"
<defaults> :=
   <def-note-duration> |
   <def-note-scale> |
   <def-beats>
<def-note-duration> := "d=" <duration>
<def-note-scale> := "o=" <scale>
<def-beats> := "b=" <beats-per-minute>
<beats-per-minute> := 25,28,...,900 ; decimal value
; If not specified, defaults are
   ;
   ; 4 = duration
   ; 6 = scale
   ; 63 = beats-per-minute
<note-command> :=
   [<duration>] <note> [<scale>] [<special-duration>] <delimiter>
   <duration> :=
   "1" | ; Full 1/1 note
   "2" | ; 1/2 note
   "4" | ; 1/4 note
   "8" | ; 1/8 note
   "16" | ; 1/16 note
   "32" | ; 1/32 note
<note> :=
   "P"  | ; pause
   "C"  |
   "C#" |
   "D"  |
   "D#" |
   "E"  |
   "F"  |
   "F#" |
   "G"  |
   "G#" |
   "A"  |
   "A#" |
   "B"
<scale> :=
   "5" | ; Note A is 440Hz
   "6" | ; Note A is 880Hz
   "7" | ; Note A is 1.76 kHz
   "8" ; Note A is 3.52 kHz
<special-duration> :=
   "." ; Dotted note
<delimiter> := ","
@endverbatim
*
*  @param[in]  melody New melody to play on buzzer.
*
**/
/******************************************************************************/
void BUZZER_PlayMusic (const u8 *melody )
   {
   u8    c;
   u8    default_id  = 0;
   u16   default_val = 0;

   DefaultOctave      = OCT_880;  // Default for the default Octave.
   DefaultDuration    = 4;        // Default for the default Duration.
   DefaultBeats       = 63;
   CurrentMelody      = melody;
   CurrentMelodySTART = melody;

   while( *CurrentMelody != RTTTL_SEP )
      {
      if( *CurrentMelody == 0 ) 
         {
         return;
         }

      // Discard the melody name.
      CurrentMelody++; 
      }

   // Now read the defaults if any.
   for( ++CurrentMelody; *CurrentMelody != RTTTL_SEP; CurrentMelody++ )
      {
      if( *CurrentMelody == 0 ) 
         {
         return;
         }

      // Discard any blank.
      while ( *CurrentMelody == ' ' ) 
         {
         CurrentMelody++;
         }

      c = *CurrentMelody;

      if ( c == RTTTL_SEP )
         {
         break;
         }

      if ( (c >= 'a') && (c <= 'z') )
         {
         c+=('A'-'a');
         }

      if ( (c >= 'A') && (c <= 'Z') )
         {
         default_id = c;
         continue;
         }

      if ( (c >= '0') && (c <= '9') )
         {
         default_val *= 10;
         default_val += (c-'0');
         c = * (CurrentMelody + 1 );

         if ( (c >= '0') && (c <= '9') )
            {
            continue;
            }

         if ( default_id == 'D' )
            {
            DefaultDuration = default_val;
            }
         else if ( default_id == 'O' )
            {
            DefaultOctave = default_val - 5;

            if ( DefaultOctave > OCT_7040 )
               DefaultOctave = OCT_440;
            }
         else if ( default_id == 'B' )
            {
            DefaultBeats = default_val;

            if ( ( DefaultBeats == 0 ) || ( DefaultBeats > 500 ) )
               DefaultBeats = 63;
            }

         default_val = 0;
         default_id  = 0;
         }
      }

   BUZZER_SetMode( BUZZER_PLAYMUSIC );
   }
