#include "../macros.c"
#include "../globals.c"
#include "../preds.c"
#include "masks.c"

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

#define all_valid \ 
	\valid_read(sd) && \
	\valid(array + (0 .. MAX_SIZE - 1)) && \
	\forall integer y ; \ 
		0 <= y < index + n ==> \ 
		\valid_read( * (array + y))

#define all_separated \
	\separated(sd, array + (0 .. MAX_SIZE - 1)) && \
	\separated(sd, *(array + (0 .. MAX_SIZE - 1)))

#define separate_nodes_from_array \
	\forall integer y ; \
		0 <= y < index + n ==> \ 
		\separated( * (array + y), array + (0 .. MAX_SIZE - 1))

#define separate_all_nodes \
	\forall integer y, z; \
		0 <= y < index + n && 0 <= z < index + n && y != z ==> \
		\separated(* (array+y), *(array+z))
	


/* TODO add in to main specs
behavior some:
	assumes sd != NULL 
			&& (\exists integer j; index <= j < index + n
		&& cpumask_test_cpu(prev_cpu, sched_domain_span(array[j]))); 
	ensures \result != NULL; 										
	ensures cpumask_test_cpu(prev_cpu, sched_domain_span(\result));  //this one passes
	ensures \forall integer j; index <= j < *loop_index  
		==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j])); 

behavior none:
	assumes sd == NULL 
			|| (\forall integer j; index <= j < index + n 
		==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j]))); 
	ensures \result == NULL; 

complete behaviors;
disjoint behaviors;
*/

/*@
requires separate_nodes_from_array; 
requires separate_all_nodes; 
requires Linked : linked_n(sd, array, index, n, NULL);
requires all_valid; 

requires \valid(loop_index) && *loop_index == 0; 
requires 0 <= index < INT_MAX && 0 <= n < INT_MAX  ;
requires 0 <= prev_cpu < small_cpumask_bits; // would this be small_cpumask_bits or something else? 	

assigns \result, *loop_index;
*/
struct sched_domain* testing_loop_1(struct sched_domain* sd, int prev_cpu)
/*@ ghost (struct sched_domain** array, int index, int n, int \ghost* loop_index) */ //TODO fix this to use 
{
	/*@	
	    loop invariant 0 <= *loop_index <= index + n ;
		loop invariant linked_n(sd, array, index + (*loop_index), n - (*loop_index), NULL);
		loop invariant \forall integer j; 0 <= j < *loop_index 
			==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j])); 
		loop assigns sd, *loop_index; 
		loop variant index + n - *loop_index; 
	*/
	while (sd && !cpumask_test_cpu(prev_cpu, sched_domain_span(sd))){ //need valid_read of all sd passed to sched_domain_span to maintain loop invariant 3
		//@ ghost (*loop_index)++; 
		sd = sd->parent; 
		//@ assert sd == NULL || \valid(sd); 
	}
			
	return sd; 
}