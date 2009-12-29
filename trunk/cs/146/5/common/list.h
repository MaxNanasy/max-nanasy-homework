#ifndef LIST_H
#define LIST_H

#include <stdbool.h>

typedef struct list {
  void *head;
  struct list *tail;
} *List;

typedef struct queue {
  List firstList, lastList;
} *Queue;
Queue newQueue ();
bool queueIsEmpty (Queue);
void enqueue (void *, Queue);
void *dequeue (Queue);

typedef struct stack {
  List list;
} *Stack;
Stack newStack ();
bool stackIsEmpty (Stack);
void push (void *, Stack);
void *pop (Stack);

#endif
