//#ifdef _IN_LIST_MAIN_FILE

#define INT_MAX 2147483647
#define MAX_SIZE INT_MAX-1
#define NULL ((void*) 0)

struct list {
  struct list *next;
  int k;
};

typedef struct list ** list_t ;

/*@
  inductive linked_n{L}(
    struct list *root, 
    struct list **array, 
    integer index, 
    integer n, 
    struct list *bound
  )
  {
    case linked_n_bound{L}:
      \forall struct list **array, *bound, integer index ;
	0 <= index <= MAX_SIZE ==>
	  linked_n(bound, array, index, 0, bound);
        
    case linked_n_cons{L}:
      \forall struct list *root, **array, *bound, integer index, n ;
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
  requires linked_n(*list, array, index, n, NULL);
  
  assigns \nothing;

  ensures \result == n ;
*/

int list_length( list_t list ) /*@ ghost (struct list **array, int index, int n) */
{ 
  struct list *l;
  int length = 0;

  /*@
    loop invariant index <= index + length <= index + n ;
    loop invariant linked_n(l, array, index+length, n-length, NULL);
    loop assigns length, l ;
    loop variant n - length ;
  */
  for(l = *list; l != NULL; l = l->next) {
    ++length;
  }

  return length;
}