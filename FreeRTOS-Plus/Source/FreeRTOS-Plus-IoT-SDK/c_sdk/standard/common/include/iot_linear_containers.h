/*
 * Amazon FreeRTOS Common V1.0.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_linear_containers.h
 * @brief Declares and implements doubly-linked lists and queues.
 */

#ifndef IOT_LINEAR_CONTAINERS_H_
#define IOT_LINEAR_CONTAINERS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * @defgroup linear_containers_datatypes_listqueue List and queue
 * @brief Structures that represent a list or queue.
 */

/**
 * @ingroup linear_containers_datatypes_listqueue
 * @brief Link member placed in structs of a list or queue.
 *
 * All elements in a list or queue must contain one of these members. The macro
 * #IotLink_Container can be used to calculate the starting address of the
 * link's container.
 */
typedef struct IotLink
{
    struct IotLink * pPrevious; /**< @brief Pointer to the previous element. */
    struct IotLink * pNext;     /**< @brief Pointer to the next element. */
} IotLink_t;

/**
 * @ingroup linear_containers_datatypes_listqueue
 * @brief Represents a doubly-linked list.
 */
typedef IotLink_t   IotListDouble_t;

/**
 * @ingroup linear_containers_datatypes_listqueue
 * @brief Represents a queue.
 */
typedef IotLink_t   IotDeQueue_t;

/**
 * @constantspage{linear_containers,linear containers library}
 *
 * @section linear_containers_constants_initializers Linear Containers Initializers
 * @brief Provides default values for initializing the linear containers data types.
 *
 * @snippet this define_linear_containers_initializers
 *
 * All user-facing data types of the linear containers library should be initialized
 * using one of the following.
 *
 * @warning Failure to initialize a linear containers data type with the appropriate
 * initializer may result in a runtime error!
 * @note The initializers may change at any time in future versions, but their
 * names will remain the same.
 */
/* @[define_linear_containers_initializers] */
#define IOT_LINK_INITIALIZER           { 0 }                /**< @brief Initializer for an #IotLink_t. */
#define IOT_LIST_DOUBLE_INITIALIZER    IOT_LINK_INITIALIZER /**< @brief Initializer for an #IotListDouble_t. */
#define IOT_DEQUEUE_INITIALIZER        IOT_LINK_INITIALIZER /**< @brief Initializer for an #IotDeQueue_t. */
/* @[define_linear_containers_initializers] */

/**
 * @def IotContainers_Assert( expression )
 * @brief Assertion macro for the linear containers library.
 *
 * Set @ref IOT_CONTAINERS_ENABLE_ASSERTS to `1` to enable assertions in the linear
 * containers library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if IOT_CONTAINERS_ENABLE_ASSERTS == 1
    #ifndef IotContainers_Assert
        #include <assert.h>
        #define IotContainers_Assert( expression )    assert( expression )
    #endif
#else
    #define IotContainers_Assert( expression )
#endif

/**
 * @brief Calculates the starting address of a containing struct.
 *
 * @param[in] type Type of the containing struct.
 * @param[in] pLink Pointer to a link member.
 * @param[in] linkName Name of the #IotLink_t in the containing struct.
 */
#define IotLink_Container( type, pLink, linkName ) \
    ( ( type * ) ( void * ) ( ( ( uint8_t * ) ( pLink ) ) - offsetof( type, linkName ) ) )

/**
 * @brief Iterates through all elements of a linear container.
 *
 * Container elements must not be freed or removed while iterating.
 *
 * @param[in] pStart The first element to iterate from.
 * @param[out] pLink Pointer to a container element.
 */
#define IotContainers_ForEach( pStart, pLink )  \
    for( ( pLink ) = ( pStart )->pNext;         \
         ( pLink ) != ( pStart );               \
         ( pLink ) = ( pLink )->pNext )

/**
 * @functionspage{linear_containers,linear containers library}
 * - @functionname{linear_containers_function_link_islinked}
 * - @functionname{linear_containers_function_list_double_create}
 * - @functionname{linear_containers_function_list_double_count}
 * - @functionname{linear_containers_function_list_double_isempty}
 * - @functionname{linear_containers_function_list_double_peekhead}
 * - @functionname{linear_containers_function_list_double_peektail}
 * - @functionname{linear_containers_function_list_double_inserthead}
 * - @functionname{linear_containers_function_list_double_inserttail}
 * - @functionname{linear_containers_function_list_double_insertbefore}
 * - @functionname{linear_containers_function_list_double_insertafter}
 * - @functionname{linear_containers_function_list_double_insertsorted}
 * - @functionname{linear_containers_function_list_double_remove}
 * - @functionname{linear_containers_function_list_double_removehead}
 * - @functionname{linear_containers_function_list_double_removetail}
 * - @functionname{linear_containers_function_list_double_removeall}
 * - @functionname{linear_containers_function_list_double_findfirstmatch}
 * - @functionname{linear_containers_function_list_double_removefirstmatch}
 * - @functionname{linear_containers_function_list_double_removeallmatches}
 * - @functionname{linear_containers_function_queue_create}
 * - @functionname{linear_containers_function_queue_count}
 * - @functionname{linear_containers_function_queue_isempty}
 * - @functionname{linear_containers_function_queue_peekhead}
 * - @functionname{linear_containers_function_queue_peektail}
 * - @functionname{linear_containers_function_queue_enqueuehead}
 * - @functionname{linear_containers_function_queue_dequeuehead}
 * - @functionname{linear_containers_function_queue_enqueuetail}
 * - @functionname{linear_containers_function_queue_dequeuetail}
 * - @functionname{linear_containers_function_queue_remove}
 * - @functionname{linear_containers_function_queue_removeall}
 * - @functionname{linear_containers_function_queue_removeallmatches}
 */

/**
 * @functionpage{IotLink_IsLinked,linear_containers,link_islinked}
 * @functionpage{IotListDouble_Create,linear_containers,list_double_create}
 * @functionpage{IotListDouble_Count,linear_containers,list_double_count}
 * @functionpage{IotListDouble_IsEmpty,linear_containers,list_double_isempty}
 * @functionpage{IotListDouble_PeekHead,linear_containers,list_double_peekhead}
 * @functionpage{IotListDouble_PeekTail,linear_containers,list_double_peektail}
 * @functionpage{IotListDouble_InsertHead,linear_containers,list_double_inserthead}
 * @functionpage{IotListDouble_InsertTail,linear_containers,list_double_inserttail}
 * @functionpage{IotListDouble_InsertBefore,linear_containers,list_double_insertbefore}
 * @functionpage{IotListDouble_InsertAfter,linear_containers,list_double_insertafter}
 * @functionpage{IotListDouble_InsertSorted,linear_containers,list_double_insertsorted}
 * @functionpage{IotListDouble_Remove,linear_containers,list_double_remove}
 * @functionpage{IotListDouble_RemoveHead,linear_containers,list_double_removehead}
 * @functionpage{IotListDouble_RemoveTail,linear_containers,list_double_removetail}
 * @functionpage{IotListDouble_RemoveAll,linear_containers,list_double_removeall}
 * @functionpage{IotListDouble_FindFirstMatch,linear_containers,list_double_findfirstmatch}
 * @functionpage{IotListDouble_RemoveFirstMatch,linear_containers,list_double_removefirstmatch}
 * @functionpage{IotListDouble_RemoveAllMatches,linear_containers,list_double_removeallmatches}
 * @functionpage{IotDeQueue_Create,linear_containers,queue_create}
 * @functionpage{IotDeQueue_Count,linear_containers,queue_count}
 * @functionpage{IotDeQueue_IsEmpty,linear_containers,queue_isempty}
 * @functionpage{IotDeQueue_PeekHead,linear_containers,queue_peekhead}
 * @functionpage{IotDeQueue_PeekTail,linear_containers,queue_peektail}
 * @functionpage{IotDeQueue_EnqueueHead,linear_containers,queue_enqueuehead}
 * @functionpage{IotDeQueue_DequeueHead,linear_containers,queue_dequeuehead}
 * @functionpage{IotDeQueue_EnqueueTail,linear_containers,queue_enqueuetail}
 * @functionpage{IotDeQueue_DequeueTail,linear_containers,queue_dequeuetail}
 * @functionpage{IotDeQueue_Remove,linear_containers,queue_remove}
 * @functionpage{IotDeQueue_RemoveAll,linear_containers,queue_removeall}
 * @functionpage{IotDeQueue_RemoveAllMatches,linear_containers,queue_removeallmatches}
 */

/**
 * @brief Check if an #IotLink_t is linked in a list or queue.
 *
 * @param[in] pLink The link to check.
 *
 * @return `true` if `pCurrent` is linked in a list or queue; `false` otherwise.
 */
/* @[declare_linear_containers_link_islinked] */
static inline bool IotLink_IsLinked( const IotLink_t * const pLink )
/* @[declare_linear_containers_link_islinked] */
{
    bool isLinked = false;

    if( pLink != NULL )
    {
        isLinked = ( pLink->pNext != NULL ) && ( pLink->pPrevious != NULL );
    }

    return isLinked;
}

/**
 * @brief Create a new doubly-linked list.
 *
 * This function initializes a new doubly-linked list. It must be called on an
 * uninitialized #IotListDouble_t before calling any other doubly-linked list
 * function. This function must not be called on an already-initialized
 * #IotListDouble_t.
 *
 * This function will not fail. The function @ref linear_containers_function_list_double_removeall
 * may be called to destroy a list.
 *
 * @param[in] pList Pointer to the memory that will hold the new doubly-linked list.
 */
/* @[declare_linear_containers_list_double_create] */
static inline void IotListDouble_Create( IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_create] */
{
    /* This function must not be called with a NULL parameter. */
    IotContainers_Assert( pList != NULL );

    /* An empty list is a link pointing to itself. */
    pList->pPrevious = pList;
    pList->pNext = pList;
}

/**
 * @brief Return the number of elements contained in an #IotListDouble_t.
 *
 * @param[in] pList The doubly-linked list with the elements to count.
 *
 * @return The number of elements in the doubly-linked list.
 */
/* @[declare_linear_containers_list_double_count] */
static inline size_t IotListDouble_Count( const IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_count] */
{
    size_t count = 0;

    if( pList != NULL )
    {
        /* Get the list head. */
        const IotLink_t * pCurrent = pList->pNext;

        /* Iterate through the list to count the elements. */
        while( pCurrent != pList )
        {
            count++;
            pCurrent = pCurrent->pNext;
        }
    }

    return count;
}

/**
 * @brief Check if a doubly-linked list is empty.
 *
 * @param[in] pList The doubly-linked list to check.
 *
 * @return `true` if the list is empty; `false` otherwise.
 */
/* @[declare_linear_containers_list_double_isempty] */
static inline bool IotListDouble_IsEmpty( const IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_isempty] */
{
    /* An empty list is NULL link, or a link pointing to itself. */
    return( ( pList == NULL ) || ( pList->pNext == pList ) );
}

/**
 * @brief Return an #IotLink_t representing the first element in a doubly-linked list
 * without removing it.
 *
 * @param[in] pList The list to peek.
 *
 * @return Pointer to an #IotLink_t representing the element at the head of the
 * list; `NULL` if the list is empty. The macro #IotLink_Container may be used to
 * determine the address of the link's container.
 */
/* @[declare_linear_containers_list_double_peekhead] */
static inline IotLink_t * IotListDouble_PeekHead( const IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_peekhead] */
{
    IotLink_t * pHead = NULL;

    if( pList != NULL )
    {
        if( IotListDouble_IsEmpty( pList ) == false )
        {
            pHead = pList->pNext;
        }
    }

    return pHead;
}

/**
 * @brief Return an #IotLink_t representing the last element in a doubly-linked
 * list without removing it.
 *
 * @param[in] pList The list to peek.
 *
 * @return Pointer to an #IotLink_t representing the element at the tail of the
 * list; `NULL` if the list is empty. The macro #IotLink_Container may be used to
 * determine the address of the link's container.
 */
/* @[declare_linear_containers_list_double_peektail] */
static inline IotLink_t * IotListDouble_PeekTail( const IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_peektail] */
{
    IotLink_t * pTail = NULL;

    if( pList != NULL )
    {
        if( IotListDouble_IsEmpty( pList ) == false )
        {
            pTail = pList->pPrevious;
        }
    }

    return pTail;
}

/**
 * @brief Insert an element at the head of a doubly-linked list.
 *
 * @param[in] pList The doubly-linked list that will hold the new element.
 * @param[in] pLink Pointer to the new element's link member.
 */
/* @[declare_linear_containers_list_double_inserthead] */
static inline void IotListDouble_InsertHead( IotListDouble_t * const pList,
                                             IotLink_t * const pLink )
/* @[declare_linear_containers_list_double_inserthead] */
{
    /* This function must not be called with NULL parameters. */
    IotContainers_Assert( pList != NULL );
    IotContainers_Assert( pLink != NULL );

    /* Save current list head. */
    IotLink_t * pHead = pList->pNext;

    /* Place new element before list head. */
    pLink->pNext = pHead;
    pLink->pPrevious = pList;

    /* Assign new list head. */
    pHead->pPrevious = pLink;
    pList->pNext = pLink;
}

/**
 * @brief Insert an element at the tail of a doubly-linked list.
 *
 * @param[in] pList The double-linked list that will hold the new element.
 * @param[in] pLink Pointer to the new element's link member.
 */
/* @[declare_linear_containers_list_double_inserttail] */
static inline void IotListDouble_InsertTail( IotListDouble_t * const pList,
                                             IotLink_t * const pLink )
/* @[declare_linear_containers_list_double_inserttail] */
{
    /* This function must not be called with NULL parameters. */
    IotContainers_Assert( pList != NULL );
    IotContainers_Assert( pLink != NULL );

    /* Save current list tail. */
    IotLink_t * pTail = pList->pPrevious;

    pLink->pNext = pList;
    pLink->pPrevious = pTail;

    pList->pPrevious = pLink;
    pTail->pNext = pLink;
}

/**
 * @brief Insert an element before another element in a doubly-linked list.
 *
 * @param[in] pElement The new element will be placed before this element.
 * @param[in] pLink Pointer to the new element's link member.
 */
/* @[declare_linear_containers_list_double_insertbefore] */
static inline void IotListDouble_InsertBefore( IotLink_t * const pElement,
                                               IotLink_t * const pLink )
/* @[declare_linear_containers_list_double_insertbefore] */
{
    IotListDouble_InsertTail( pElement, pLink );
}

/**
 * @brief Insert an element after another element in a doubly-linked list.
 *
 * @param[in] pElement The new element will be placed after this element.
 * @param[in] pLink Pointer to the new element's link member.
 */
/* @[declare_linear_containers_list_double_insertafter] */
static inline void IotListDouble_InsertAfter( IotLink_t * const pElement,
                                              IotLink_t * const pLink )
/* @[declare_linear_containers_list_double_insertafter] */
{
    IotListDouble_InsertHead( pElement, pLink );
}

/**
 * @brief Insert an element in a sorted doubly-linked list.
 *
 * Places an element into a list by sorting it into order. The function
 * `compare` is used to determine where to place the new element.
 *
 * @param[in] pList The list that will hold the new element.
 * @param[in] pLink Pointer to the new element's link member.
 * @param[in] compare Determines the order of the list. Returns a negative
 * value if its first argument is less than its second argument; returns
 * zero if its first argument is equal to its second argument; returns a
 * positive value if its first argument is greater than its second argument.
 * The parameters to this function are #IotLink_t, so the macro #IotLink_Container
 * may be used to determine the address of the link's container.
 */
/* @[declare_linear_containers_list_double_insertsorted] */
static inline void IotListDouble_InsertSorted( IotListDouble_t * const pList,
                                               IotLink_t * const pLink,
                                               int32_t ( *compare )( const IotLink_t * const, const IotLink_t * const ) )
/* @[declare_linear_containers_list_double_insertsorted] */
{
    /* This function must not be called with NULL parameters. */
    IotContainers_Assert( pList != NULL );
    IotContainers_Assert( pLink != NULL );
    IotContainers_Assert( compare != NULL );

    /* Insert at head for empty list. */
    if( IotListDouble_IsEmpty( pList ) == true )
    {
        IotListDouble_InsertHead( pList, pLink );
    }
    else
    {
        bool inserted = false;
        IotLink_t * pCurrent = pList->pNext;

        /* Iterate through the list to find the correct position. */
        while( pCurrent != pList )
        {
            /* Comparing for '<' preserves the order of insertion. */
            if( compare( pLink, pCurrent ) < 0 )
            {
                IotListDouble_InsertBefore( pCurrent, pLink );
                inserted = true;

                break;
            }

            pCurrent = pCurrent->pNext;
        }

        /* New element is greater than all elements in list. Insert at tail. */
        if( inserted == false )
        {
            IotListDouble_InsertTail( pList, pLink );
        }
    }
}

/**
 * @brief Remove a single element from a doubly-linked list.
 *
 * @param[in] pLink The element to remove.
 */
/* @[declare_linear_containers_list_double_remove] */
static inline void IotListDouble_Remove( IotLink_t * const pLink )
/* @[declare_linear_containers_list_double_remove] */
{
    /* This function must not be called with a NULL parameter. */
    IotContainers_Assert( pLink != NULL );

    /* This function must be called on a linked element. */
    IotContainers_Assert( IotLink_IsLinked( pLink ) == true );

    pLink->pPrevious->pNext = pLink->pNext;
    pLink->pNext->pPrevious = pLink->pPrevious;
    pLink->pPrevious = NULL;
    pLink->pNext = NULL;
}

/**
 * @brief Remove the element at the head of a doubly-linked list.
 *
 * @param[in] pList The doubly-linked list that holds the element to remove.
 *
 * @return Pointer to an #IotLink_t representing the removed list head; `NULL`
 * if the list is empty. The macro #IotLink_Container may be used to determine
 * the address of the link's container.
 */
/* @[declare_linear_containers_list_double_removehead] */
static inline IotLink_t * IotListDouble_RemoveHead( IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_removehead] */
{
    IotLink_t * pHead = NULL;

    if( IotListDouble_IsEmpty( pList ) == false )
    {
        pHead = pList->pNext;
        IotListDouble_Remove( pHead );
    }

    return pHead;
}

/**
 * @brief Remove the element at the tail of a doubly-linked list.
 *
 * @param[in] pList The doubly-linked list that holds the element to remove.
 *
 * @return Pointer to an #IotLink_t representing the removed list tail; `NULL`
 * if the list is empty. The macro #IotLink_Container may be used to determine
 * the address of the link's container.
 */
/* @[declare_linear_containers_list_double_removetail] */
static inline IotLink_t * IotListDouble_RemoveTail( IotListDouble_t * const pList )
/* @[declare_linear_containers_list_double_removetail] */
{
    IotLink_t * pTail = NULL;

    if( IotListDouble_IsEmpty( pList ) == false )
    {
        pTail = pList->pPrevious;
        IotListDouble_Remove( pTail );
    }

    return pTail;
}

/**
 * @brief Remove all elements in a doubly-linked list.
 *
 * @param[in] pList The list to empty.
 * @param[in] freeElement A function to free memory used by each removed list
 * element. Optional; pass `NULL` to ignore.
 * @param[in] linkOffset Offset in bytes of a link member in its container, used
 * to calculate the pointer to pass to `freeElement`. This value should be calculated
 * with the C `offsetof` macro. This parameter is ignored if `freeElement` is `NULL`
 * or its value is `0`.
 */
/* @[declare_linear_containers_list_double_removeall] */
static inline void IotListDouble_RemoveAll( IotListDouble_t * const pList,
                                            void ( *freeElement )( void * ),
                                            size_t linkOffset )
/* @[declare_linear_containers_list_double_removeall] */
{
    /* This function must not be called with a NULL pList parameter. */
    IotContainers_Assert( pList != NULL );

    /* Get the list head. */
    IotLink_t * pCurrent = pList->pNext;

    /* Iterate through the list and remove all elements. */
    while( pCurrent != pList )
    {
        /* Save a pointer to the next list element. */
        IotLink_t * pNext = pCurrent->pNext;

        /* Remove and free the current list element. */
        IotListDouble_Remove( pCurrent );

        if( freeElement != NULL )
        {
            freeElement( ( ( uint8_t * ) pCurrent ) - linkOffset );
        }

        /* Move the iterating pointer to the next list element. */
        pCurrent = pNext;
    }
}

/**
 * @brief Search a doubly-linked list for the first matching element.
 *
 * If a match is found, the matching element is <b>not</b> removed from the list.
 * See @ref linear_containers_function_list_double_removefirstmatch for the function
 * that searches and removes.
 *
 * @param[in] pList The doubly-linked list to search.
 * @param[in] pStartPoint An element in `pList`. Only elements between this one and
 * the list tail are checked. Pass `NULL` to search from the beginning of the list.
 * @param[in] isMatch Function to determine if an element matches. Pass `NULL` to
 * search using the address `pMatch`, i.e. `element == pMatch`.
 * @param[in] pMatch If `isMatch` is `NULL`, each element in the list is compared
 * to this address to find a match. Otherwise, it is passed as the second argument
 * to `isMatch`.
 *
 * @return Pointer to an #IotLink_t representing the first matched element; `NULL`
 * if no match is found. The macro #IotLink_Container may be used to determine the
 * address of the link's container.
 */
/* @[declare_linear_containers_list_double_findfirstmatch] */
static inline IotLink_t * IotListDouble_FindFirstMatch( const IotListDouble_t * const pList,
                                                        const IotLink_t * const pStartPoint,
                                                        bool ( *isMatch )( const IotLink_t * const, void * ),
                                                        void * pMatch )
/* @[declare_linear_containers_list_double_findfirstmatch] */
{
    /* The const must be cast away to match this function's return value. Nevertheless,
     * this function will respect the const-ness of pStartPoint. */
    IotLink_t * pCurrent = ( IotLink_t * ) pStartPoint;

    /* This function must not be called with a NULL pList parameter. */
    IotContainers_Assert( pList != NULL );

    /* Search starting from list head if no start point is given. */
    if( pStartPoint == NULL )
    {
        pCurrent = pList->pNext;
    }

    /* Iterate through the list to search for matches. */
    while( pCurrent != pList )
    {
        /* Call isMatch if provided. Otherwise, compare pointers. */
        if( isMatch != NULL )
        {
            if( isMatch( pCurrent, pMatch ) == true )
            {
                return pCurrent;
            }
        }
        else
        {
            if( pCurrent == pMatch )
            {
                return pCurrent;
            }
        }

        pCurrent = pCurrent->pNext;
    }

    /* No match found, return NULL. */
    return NULL;
}

/**
 * @brief Search a doubly-linked list for the first matching element and remove
 * it.
 *
 * An #IotLink_t may be passed as `pList` to start searching after the head of a
 * doubly-linked list.
 *
 * @param[in] pList The doubly-linked list to search.
 * @param[in] pStartPoint An element in `pList`. Only elements between this one and
 * the list tail are checked. Pass `NULL` to search from the beginning of the list.
 * @param[in] isMatch Function to determine if an element matches. Pass `NULL` to
 * search using the address `pMatch`, i.e. `element == pMatch`.
 * @param[in] pMatch If `isMatch` is `NULL`, each element in the list is compared
 * to this address to find a match. Otherwise, it is passed as the second argument
 * to `isMatch`.
 *
 * @return Pointer to an #IotLink_t representing the matched and removed element;
 * `NULL` if no match is found. The macro #IotLink_Container may be used to determine
 * the address of the link's container.
 */
/* @[declare_linear_containers_list_double_removefirstmatch] */
static inline IotLink_t * IotListDouble_RemoveFirstMatch( IotListDouble_t * const pList,
                                                          const IotLink_t * const pStartPoint,
                                                          bool ( *isMatch )( const IotLink_t *, void * ),
                                                          void * pMatch )
/* @[declare_linear_containers_list_double_removefirstmatch] */
{
    IotLink_t * pMatchedElement = IotListDouble_FindFirstMatch( pList,
                                                                pStartPoint,
                                                                isMatch,
                                                                pMatch );

    if( pMatchedElement != NULL )
    {
        IotListDouble_Remove( pMatchedElement );
    }

    return pMatchedElement;
}

/**
 * @brief Remove all matching elements from a doubly-linked list.
 *
 * @param[in] pList The doubly-linked list to search.
 * @param[in] isMatch Function to determine if an element matches. Pass `NULL` to
 * search using the address `pMatch`, i.e. `element == pMatch`.
 * @param[in] pMatch If `isMatch` is `NULL`, each element in the list is compared
 * to this address to find a match. Otherwise, it is passed as the second argument
 * to `isMatch`.
 * @param[in] freeElement A function to free memory used by each removed list
 * element. Optional; pass `NULL` to ignore.
 * @param[in] linkOffset Offset in bytes of a link member in its container, used
 * to calculate the pointer to pass to `freeElement`. This value should be calculated
 * with the C `offsetof` macro. This parameter is ignored if `freeElement` is `NULL`
 * or its value is `0`.
 */
/* @[declare_linear_containers_list_double_removeallmatches] */
static inline void IotListDouble_RemoveAllMatches( IotListDouble_t * const pList,
                                                   bool ( *isMatch )( const IotLink_t *, void * ),
                                                   void * pMatch,
                                                   void ( *freeElement )( void * ),
                                                   size_t linkOffset )
/* @[declare_linear_containers_list_double_removeallmatches] */
{
    IotLink_t * pMatchedElement = NULL, * pNextElement = NULL;

    /* Search the list for all matching elements. */
    do
    {
        pMatchedElement = IotListDouble_FindFirstMatch( pList,
                                                        pMatchedElement,
                                                        isMatch,
                                                        pMatch );

        if( pMatchedElement != NULL )
        {
            /* Save pointer to next element. */
            pNextElement = pMatchedElement->pNext;

            /* Match found; remove and free. */
            IotListDouble_Remove( pMatchedElement );

            if( freeElement != NULL )
            {
                freeElement( ( ( uint8_t * ) pMatchedElement ) - linkOffset );
            }

            /* Continue search from next element. */
            pMatchedElement = pNextElement;
        }
    } while( pMatchedElement != NULL );
}

/**
 * @brief Create a new queue.
 *
 * This function initializes a new double-ended queue. It must be called on an uninitialized
 * #IotDeQueue_t before calling any other queue function. This function must not be
 * called on an already-initialized #IotDeQueue_t.
 *
 * This function will not fail.
 *
 * @param[in] pQueue Pointer to the memory that will hold the new queue.
 */
/* @[declare_linear_containers_queue_create] */
static inline void IotDeQueue_Create( IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_create] */
{
    IotListDouble_Create( pQueue );
}

/**
 * @brief Return the number of elements contained in an #IotDeQueue_t.
 *
 * @param[in] pQueue The queue with the elements to count.
 *
 * @return The number of items elements in the queue.
 */
/* @[declare_linear_containers_queue_count] */
static inline size_t IotDeQueue_Count( const IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_count] */
{
    return IotListDouble_Count( pQueue );
}

/**
 * @brief Check if a queue is empty.
 *
 * @param[in] pQueue The queue to check.
 *
 * @return `true` if the queue is empty; `false` otherwise.
 *
 */
/* @[declare_linear_containers_queue_isempty] */
static inline bool IotDeQueue_IsEmpty( const IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_isempty] */
{
    return IotListDouble_IsEmpty( pQueue );
}

/**
 * @brief Return an #IotLink_t representing the element at the front of the queue
 * without removing it.
 *
 * @param[in] pQueue The queue to peek.
 *
 * @return Pointer to an #IotLink_t representing the element at the head of the
 * queue; `NULL` if the queue is empty. The macro #IotLink_Container may be used
 * to determine the address of the link's container.
 */
/* @[declare_linear_containers_queue_peekhead] */
static inline IotLink_t * IotDeQueue_PeekHead( const IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_peekhead] */
{
    return IotListDouble_PeekHead( pQueue );
}

/**
 * @brief Return an #IotLink_t representing the element at the back of the queue
 * without removing it.
 *
 * @param[in] pQueue The queue to peek.
 *
 * @return Pointer to an #IotLink_t representing the element at the head of the
 * queue; `NULL` if the queue is empty. The macro #IotLink_Container may be used
 * to determine the address of the link's container.
 */
/* @[declare_linear_containers_queue_peektail] */
static inline IotLink_t * IotDeQueue_PeekTail( const IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_peektail] */
{
    return IotListDouble_PeekTail( pQueue );
}

/**
 * @brief Add an element at the head of the queue.
 *
 * @param[in] pQueue The queue that will hold the new element.
 * @param[in] pLink Pointer to the new element's link member.
 */
/* @[declare_linear_containers_queue_enqueuehead] */
static inline void IotDeQueue_EnqueueHead( IotDeQueue_t * const pQueue,
                                     IotLink_t * const pLink )
/* @[declare_linear_containers_queue_enqueuehead] */
{
    IotListDouble_InsertHead( pQueue, pLink );
}

/**
 * @brief Remove an element at the head of the queue.
 *
 * @param[in] pQueue The queue that holds the element to remove.
 *
 * @return Pointer to an #IotLink_t representing the removed queue element; `NULL`
 * if the queue is empty. The macro #IotLink_Container may be used to determine
 * the address of the link's container.
 */
/* @[declare_linear_containers_queue_dequeuehead] */
static inline IotLink_t * IotDeQueue_DequeueHead( IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_dequeuehead] */
{
    return IotListDouble_RemoveHead( pQueue );
}

/**
 * @brief Add an element at the tail of the queue.
 *
 * @param[in] pQueue The queue that will hold the new element.
 * @param[in] pLink Pointer to the new element's link member.
 */
/* @[declare_linear_containers_queue_enqueuetail] */
static inline void IotDeQueue_EnqueueTail( IotDeQueue_t * const pQueue,
                                     IotLink_t * const pLink )
/* @[declare_linear_containers_queue_enqueuetail] */
{
    IotListDouble_InsertTail( pQueue, pLink );
}

/**
 * @brief Remove an element at the tail of the queue.
 *
 * @param[in] pQueue The queue that holds the element to remove.
 *
 * @return Pointer to an #IotLink_t representing the removed queue element; `NULL`
 * if the queue is empty. The macro #IotLink_Container may be used to determine
 * the address of the link's container.
 */
/* @[declare_linear_containers_queue_dequeuetail] */
static inline IotLink_t * IotDeQueue_DequeueTail( IotDeQueue_t * const pQueue )
/* @[declare_linear_containers_queue_dequeuetail] */
{
    return IotListDouble_RemoveTail( pQueue );
}

/**
 * @brief Remove a single element from a queue.
 *
 * @param[in] pLink The element to remove.
 */
/* @[declare_linear_containers_queue_remove] */
static inline void IotDeQueue_Remove( IotLink_t * const pLink )
/* @[declare_linear_containers_queue_remove] */
{
    IotListDouble_Remove( pLink );
}

/**
 * @brief Remove all elements in a queue.
 *
 * @param[in] pQueue The queue to empty.
 * @param[in] freeElement A function to free memory used by each removed queue
 * element. Optional; pass `NULL` to ignore.
 * @param[in] linkOffset Offset in bytes of a link member in its container, used
 * to calculate the pointer to pass to `freeElement`. This value should be calculated
 * with the C `offsetof` macro. This parameter is ignored if `freeElement` is `NULL`
 * or its value is `0`.
 */
/* @[declare_linear_containers_queue_removeall] */
static inline void IotDeQueue_RemoveAll( IotDeQueue_t * const pQueue,
                                       void ( * freeElement )( void * ),
                                       size_t linkOffset )
/* @[declare_linear_containers_queue_removeall] */
{
    IotListDouble_RemoveAll( pQueue, freeElement, linkOffset );
}

/**
 * @brief Remove all matching elements from a queue.
 *
 * @param[in] pQueue The queue to search.
 * @param[in] isMatch Function to determine if an element matches. Pass `NULL` to
 * search using the address `pMatch`, i.e. `element == pMatch`.
 * @param[in] pMatch If `isMatch` is `NULL`, each element in the queue is compared
 * to this address to find a match. Otherwise, it is passed as the second argument
 * to `isMatch`.
 * @param[in] freeElement A function to free memory used by each removed queue
 * element. Optional; pass `NULL` to ignore.
 * @param[in] linkOffset Offset in bytes of a link member in its container, used
 * to calculate the pointer to pass to `freeElement`. This value should be calculated
 * with the C `offsetof` macro. This parameter is ignored if `freeElement` is `NULL`
 * or its value is `0`.
 */
/* @[declare_linear_containers_queue_removeallmatches] */
static inline void IotDeQueue_RemoveAllMatches( IotDeQueue_t * const pQueue,
                                              bool ( * isMatch )( const IotLink_t *, void * ),
                                              void * pMatch,
                                              void ( * freeElement )( void * ),
                                              size_t linkOffset )
/* @[declare_linear_containers_queue_removeallmatches] */
{
    IotListDouble_RemoveAllMatches( pQueue, isMatch, pMatch, freeElement, linkOffset );
}

#endif /* IOT_LINEAR_CONTAINERS_H_ */
