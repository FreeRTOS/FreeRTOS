#ifndef LIST_MACRO_H
#define LIST_MACRO_H

#include <FreeRTOS.h>
#include <task.h>
#include <portmacro.h>
#include <list.h>

struct tskTaskControlBlock;
typedef struct tskTaskControlBlock  TCB_t;

#undef  listLIST_IS_EMPTY
BaseType_t listLIST_IS_EMPTY( const List_t *pxList );

#undef  listGET_OWNER_OF_HEAD_ENTRY
TCB_t * listGET_OWNER_OF_HEAD_ENTRY(const  List_t * pxList );

#undef listIS_CONTAINED_WITHIN
BaseType_t listIS_CONTAINED_WITHIN( List_t * list, const ListItem_t * listItem);

#undef listGET_LIST_ITEM_VALUE
TickType_t listGET_LIST_ITEM_VALUE( ListItem_t * listItem  );

#undef listSET_LIST_ITEM_VALUE
void listSET_LIST_ITEM_VALUE( ListItem_t * listItem, TickType_t itemValue);


#undef listLIST_ITEM_CONTAINER
List_t * listLIST_ITEM_CONTAINER(const ListItem_t * listItem);

#undef listCURRENT_LIST_LENGTH
UBaseType_t listCURRENT_LIST_LENGTH(List_t * list);

#undef listGET_ITEM_VALUE_OF_HEAD_ENTRY
TickType_t listGET_ITEM_VALUE_OF_HEAD_ENTRY(List_t * list);

#undef listGET_LIST_ITEM_OWNER
TCB_t * listGET_LIST_ITEM_OWNER(ListItem_t * listItem);

#endif
