function decode_stack(sp)
{
  var i;
  var a = new Array();

  var current_task;

  current_task = Debug.evaluate("pxCurrentTCB");

  if( current_task == 0 )
    return;

  sp += 4; /* skip stored ulCriticalNesting */
  a[16] = Debug.evaluate("*(unsigned long*)" + sp); 

  for (i = 0; i <= 15; i++)
  {
    sp += 4;
    a[i] = Debug.evaluate("*(unsigned long*)" + sp); 
  }

  return a;
}

function add_task(task, state)
{
  var tcb, task_name;

  var current_task;

  current_task = Debug.evaluate("pxCurrentTCB");

  if( current_task == 0 )
    return;

  tcb = Debug.evaluate("*(tskTCB *)" + task);
  task_name = Debug.evaluate("(char*)&(*(tskTCB *)" + task + ").pcTaskName[0]");
  Threads.add("#" + tcb.uxTCBNumber + " \"" + task_name + "\"", tcb.uxPriority, state, decode_stack(tcb.pxTopOfStack));
}

function add_list(list, state, current_task)
{
  var i, index, item, end;
  var current_task;

  current_task = Debug.evaluate("pxCurrentTCB");

  if( current_task == 0 )
    return;

  if (list.uxNumberOfItems)
  {
    index = list.pxIndex;
    end = list.xListEnd;
    for (i = 0; i < list.uxNumberOfItems; i++)
    {
      item = Debug.evaluate("*(xListItem *)" + index);
      if (index != end)
      {
        task = item.pvOwner;
        if (task) add_task(task, (task == current_task) ? "executing" : state);
      }
      index = item.pxNext;
    }
  }
}

function update() 
{
  var i, current_task, list, lists, max_priority;

  Threads.clear();

  current_task = Debug.evaluate("pxCurrentTCB");

  if( current_task == 0 )
    return;

  Threads.newqueue("Ready");
  lists = Debug.evaluate("pxReadyTasksLists");
  if (lists)
  { 
    max_priority = Debug.evaluate("uxTopUsedPriority");
    max_priority = Debug.evaluate("*(long *)" + max_priority);

    for (i = 0; i <= max_priority; i++)
    {
      list = Debug.evaluate("((xList*)" + lists + ")[" + (max_priority - i) + "]");
      add_list(list, "ready", current_task);
    }
  }

  Threads.newqueue("Blocked");

  list = Debug.evaluate("pxDelayedTaskList");
  if (list)
  {
    list = Debug.evaluate("**(xList **)" + list);
    add_list(list, "blocked");
  }

  list = Debug.evaluate("pxOverflowDelayedTaskList");
  if (list)
  {
    list = Debug.evaluate("**(xList **)" + list);
    add_list(list, "blocked");
  }

  Threads.newqueue("Suspended");

  list = Debug.evaluate("xSuspendedTaskList");
  if (list)
  {
    list = Debug.evaluate("*(xList *)" + list);
    add_list(list, "suspended");
  }
}

