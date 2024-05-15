#include <limits.h>
#include "globals.c"

#define MAX_SIZE INT_MAX-1

/*@ 
  inductive linked_n{L}(
    struct sched_domain* root, 
    struct sched_domain** array, 
    integer index, 
    integer n, 
    struct sched_domain* bound
  )
  {
    case linked_n_bound{L}:
      \forall struct sched_domain** array, *bound, integer index ;
    0 <= index < INT_MAX ==>
      linked_n(bound, array, index, 0, bound);
      
    case linked_n_cons{L}:
      \forall struct sched_domain* root, **array, *bound, integer index, n ;
        0 < n ==> 0 <= index ==> 
        0 <= index + n < INT_MAX ==>
    \valid(root) ==> 
      root == array[index] ==>
    linked_n(root->parent, array, index + 1, n - 1, bound) ==>
      linked_n(root, array, index, n, bound);
  }
*/
/*@
  lemma linked_n_bounds :
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==>
        ((n == 0 && 0 <= i <= MAX_SIZE) || (n > 0 && 0 <= i < MAX_SIZE));
*/
/*@
  lemma linked_valid_range :
    \forall struct sched_domain *root, **array, *bound, *node, integer i, n ;
      n > 0 ==>
      linked_n (root, array, i, n, bound) ==> 
        \valid(array[i .. i + n -1]);
*/
/*@
  lemma linked_zero_root_equal_bound:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && n == 0 ==> root == bound;
*/
/*@
  lemma linked_root_not_bound_n_sup_zero:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && root != bound ==> n > 0;
*/
/*@
  lemma linked_next_valid:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      n > 1 ==>
      linked_n (root, array, i, n, bound) ==> 
        \valid(root->parent);
*/
/*@
  lemma linked_next_index:
    \forall struct sched_domain *root, **array, *bound, integer i, n ;
      n > 1 ==>
      linked_n (root, array, i, n, bound) ==> 
        root->parent == array[i + 1];
*/