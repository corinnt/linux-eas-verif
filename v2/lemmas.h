#include <limits.h>
#include "../globals.c"



/*@
  lemma stay_linked{L1, L2}:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n{L1} (root, array, i, n, bound) ==>
      unchanged{L1, L2}(array, i, i+n) ==>
        linked_n{L2} (root, array, i, n, bound);
*/
/*@
  lemma linked_n_starting_from_null_empty:
    \forall struct sched_domain **array, integer index, n ;
      linked_n(NULL, array, index, n, NULL) ==> n == 0;
*/
/*@
  lemma linked_n_all_elements_not_null:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==>
        (\forall integer j ; i <= j < i+n ==> array[j] != NULL) ;
*/
/*@
  lemma linked_last_next_index_bound :
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      n > 0 ==>
      linked_n (root, array, i, n, bound) ==> 
        array[i + n - 1]->parent == bound;
*/
/*@
  lemma linked_n_bounds :
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==>
        ((n == 0 && 0 <= i <= MAX_SIZE) || (n > 0 && 0 <= i < MAX_SIZE));
*/
/*@
  lemma linked_max_value_index_n:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==> i + n - 1 < MAX_SIZE ;
*/
/*@
  lemma linked_valid_range :
    \forall struct sched_domain *root, **array, *bound, *node, integer i, n ;
      n > 0 ==>
      linked_n (root, array, i, n, bound) ==> 
        \valid(array[i .. i + n -1]);
*/
/*@
  lemma linked_split_segment:
    \forall struct lsched_domainist *root, **array, *bound, *b0, integer i, n, k;
      n > 0 ==> k >= 0 ==>
        b0 == array[i + n - 1]->parent ==>
        linked_n(root, array, i, n + k, bound) ==>
          (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, k, bound));
*/
/*@
  lemma linked_split_segment_direct:
    \forall struct sched_domain *root, **array, *bound, *bound_split, 
      integer index, size, k;
      size > 0 ==> k > 0 ==>
      bound_split == array[index + size] ==>
      linked_n(root, array, index, size + k, bound) ==>
      ( linked_n(root, array, index, size, bound_split) && 
        linked_n(bound_split, array, index + size, k, bound) );
*/
/*@
  lemma linked_split_segment_left:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      n > 0 ==>
      ((linked_n(root, array, i, n, bound) <==>             
      (linked_n(root, array, i, 1, root->parent) &&
        linked_n(root->parent, array, i+1, n-1, bound))));
*/
/*@
  lemma linked_split_segment_right:
    \forall struct sched_domain *root, **array, *bound, *b0, integer i, n ;
      n > 0 ==>
        b0 == array[i + n - 1]->parent ==>
        linked_n(root, array, i, n + 1, bound) ==>
          (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, 1, bound));
*/
/*@
  lemma linked_split_segment_right_direct:
    \forall struct sched_domain *root, **array, *bound, *b0, integer i, n ;
      n > 0 ==>
        b0 == array[i + n] ==>
        linked_n(root, array, i, n + 1, bound) ==>
          (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, 1, bound));
*/
/*@
  lemma linked_merge_segment:
    \forall struct sched_domain *root, **array, *bound, *b0, integer i, n, k;
      n >= 0 ==> k >= 0 ==>
      (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, k, bound)) ==>
        linked_n(root, array, i, n + k, bound);
*/
/*@
  lemma linked_merge_segment_right:
    \forall struct sched_domain *root, **array, *bound, *b0, integer i, n ;
      n >= 0 ==>       
      (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, 1, bound)) ==>
        linked_n(root, array, i, n + 1, bound);
*/
/*@
  lemma linked_not_empty_head_position:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && n > 0 ==> root == array[i];
*/
/*@
  lemma linked_zero_root_equal_bound:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && n == 0 ==> root == bound;
*/
/*@
  lemma linked_root_not_bound_n_sup_zero:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && root != bound ==> n > 0;
*/
/*@
  lemma not_in_not_in_swipe_left{K, L}:
    \forall struct list **l, **array, integer index, n ;
      \separated(\at(l, K), \at(*(array + (index+1 .. index + n - 1)), K)) &&
      array_swipe_left{K, L} (array, index, index + n - 1) ==>
        \separated(\at(l, L), \at(*(array + (index .. index + n - 2)), L));
*/
/*@
  lemma linked_next_valid:
    \forall struct list *root, **array, *bound, integer i, n ;
      n > 1 ==>
      linked_n (root, array, i, n, bound) ==> 
        \valid(root->parent);
*/
/*@
  lemma linked_next_index:
    \forall struct list *root, **array, *bound, integer i, n ;
      n > 1 ==>
      linked_n (root, array, i, n, bound) ==> 
        root->parent == array[i + 1];
*/
/*@
  lemma index_of_not_in_subrange:
    \forall struct list *item, **array, integer down, inter, up ;
      down >= 0 && up >= 0 && inter >= down ==>
      (\forall integer i ; down <= i < inter ==> array[i] != item) ==>
        index_of(item, array, down, up) ==
        index_of(item, array, inter, up) ;
*/
/*@
  lemma index_of_unexisting_item:
    \forall struct list *item, **array, integer down, up ;
      down >= 0 && up >= 0 ==>
      (\forall integer i ; down <= i < up ==> array[i] != item) ==>
        index_of(item, array, down, up) == up ;
*/
/*@
  lemma index_of_bounds:
    \forall struct list *item, **array, integer down, up ;
      0 <= down <= up ==>
      down <= index_of(item, array, down, up) <= up ;
*/
/*@
  lemma index_of_existing_item:
    \forall struct list *item, **array, integer down, up ;
      down >= 0 && up >= 0 ==>
      (\exists integer i ; down <= i < up && array[i] == item) ==>
        down <= index_of(item, array, down, up) < up ;
*/
