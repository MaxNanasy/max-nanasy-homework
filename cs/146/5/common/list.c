#include <stdlib.h>
#include "list.h"
#include "debug.h"

List cons (void *head, List tail)
{
  List list = (List) malloc (sizeof (struct list));
  debug ("Allocated List\n");
  list -> head = head;
  list -> tail = tail;
  return list;
}

void freeList (List list)
{
  if (list != NULL) {
    free (list -> head);
    freeList (list -> tail);
    free (list);
    debug ("Deallocated List\n");
  }
}

Queue newQueue ()
{
  Queue queue = (Queue) malloc (sizeof (struct queue));
  debug ("Allocated Queue\n");
  queue -> firstList = NULL;
  return queue;
}

bool queueIsEmpty (Queue queue)
{
  return queue -> firstList == NULL;
}

void enqueue (void *value, Queue queue)
{
  List lastList = queue -> lastList
     , newLastList = cons (value, NULL);
  if (queue -> firstList)
    lastList -> tail = newLastList;
  else
    queue -> firstList = newLastList;
  queue -> lastList = newLastList;
}

void *dequeue (Queue queue)
{
  List firstList = queue -> firstList;
  debug ("Allocated Queue\n");
  void *value = firstList -> head;
  queue -> firstList = firstList -> tail;
  free (firstList);
  return value;
}

void freeQueue (Queue queue)
{
  free (queue);
  debug ("Deallocated Queue\n");
}

Stack newStack ()
{
  Stack stack = (Stack) malloc (sizeof (struct stack));
  debug ("Allocated Stack\n");
  stack -> list = NULL;
}

bool stackIsEmpty (Stack stack)
{
  return stack -> list == NULL;
}

void push (void *value, Stack stack)
{
  stack -> list = cons (value, stack -> list);
}

void *pop (Stack stack)
{
  List list = stack -> list;
  void *value = list -> head;
  stack -> list = list -> tail;
  free (list);
  return value;
}

void freeStack (Stack stack)
{
  free (stack);
  debug ("Deallocated Stack\n");
}
