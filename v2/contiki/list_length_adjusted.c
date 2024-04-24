//#ifdef _IN_LIST_MAIN_FILE

#define INT_MAX 2147483647
#define MAX_SIZE INT_MAX-1
#define NULL ((void*) 0)

typedef struct node {
  struct node* next;
  int k;
} Node ;

//typedef struct node* list_t ;

/*@ 
  inductive linked_n{L}(
    Node* root, 
    Node** array, 
    integer index, 
    integer n, 
    Node* bound
  )
  {
    case linked_n_bound{L}:
      \forall Node** array, *bound, integer index ;
    0 <= index <= MAX_SIZE ==>
      linked_n(bound, array, index, 0, bound);
      
    case linked_n_cons{L}:
      \forall Node* root, **array, *bound, integer index, n ;
        0 < n ==> 0 <= index ==> 
        0 <= index + n <= MAX_SIZE ==>
    \valid(root) ==> 
      root == array[index] ==>
    linked_n(root->next, array, index + 1, n - 1, bound) ==>
      linked_n(root, array, index, n, bound);
  }
*/

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