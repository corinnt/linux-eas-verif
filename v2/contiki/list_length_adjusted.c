//#ifdef _IN_LIST_MAIN_FILE
#include "lemmas.h"
#define INT_MAX 2147483647
#define MAX_SIZE INT_MAX-1
#define NULL ((void*) 0)

typedef struct node {
  struct node* next;
  int k;
} Node ;

//typedef struct node* list_t ;

/*@
  requires \valid(list);
  requires linked_n(list, array, index, n, NULL);
  
  assigns \nothing;

  ensures \result == n ;
*/
int list_length( Node* list ) /*@ ghost (Node** array, int index, int n) */
{ 
  Node* cons;
  int length = 0;

  /*@
    loop invariant index <= index + length <= index + n ;
    loop invariant linked_n(cons, array, index+length, n-length, NULL);
    loop assigns length, cons ;
    loop variant n - length ;
  */
  for(cons = list; cons != NULL; cons = cons->next) { 
    ++length;
  }

  return length;
}