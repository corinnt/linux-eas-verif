
#include "../macros.c"
#include "../globals.c"
#include "../preds.c"
#include "masks.c"

//#include "../lemmas.h"

// NOTE: version which uses distance rather than loop_index for loop variant

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

// sd_distance dormant
/*
    logic int sd_distance(struct sched_domain* sd);
*/

/* ghost 
	/@ ensures \result == sd_distance(sd) ;
	 ensures \result >= 0 ; 
	@/
	unsigned int sd_distance(struct sched_domain* sd) {
		unsigned int distance = 0; 
		while (sd) {
			distance++;
			sd = sd->parent;
		} 
    	return distance; 
	}
*/

#define all_valid \
	\valid_read(sd) && \
	\valid(array + (0 .. MAX_SIZE - 1)) && \
	\valid(array[0 .. MAX_SIZE - 1])

#define separate_nodes_from_array \
		\separated(array[0 .. index + n], array + (0 .. MAX_SIZE - 1))

#define separate_all_nodes \
	\forall integer y, z; \
		0 <= y < index + n && 0 <= z < index + n && y != z ==> \
		\separated(* (array+y), *(array+z))

/*@
requires separate_nodes_from_array; 
requires separate_all_nodes; 
requires Linked : linked_n(sd, array, index, n, NULL);
requires all_valid; 

requires loop_index == index && \at(loop_index, Pre) == 0 && \at(index, Pre) == 0; 
requires 0 <= n < INT_MAX;
requires 0 <= prev_cpu < small_cpumask_bits; 

assigns \result;

behavior some:
	assumes sd != NULL 
			&& (\exists integer j; index <= j < index + n
		&& cpumask_test_cpu(prev_cpu, sched_domain_span(array[j])));  										
	ensures result_in_mask: cpumask_test_cpu(prev_cpu, sched_domain_span(\result));
	ensures result_is_min: \forall integer j; index <= j < \at(loop_index, Post)
		==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j])); 
	ensures result_not_null: \result != NULL;

behavior none:
	assumes sd == NULL 
			|| (\forall integer j; index <= j < index + n 
		==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j]))); 
	ensures result_is_null: \result == NULL; 

complete behaviors;
disjoint behaviors;
*/
struct sched_domain* testing_loop_1(struct sched_domain* sd, int prev_cpu)
/*@ ghost (struct sched_domain** array, int index, int n, int loop_index) */ 
{
	/*@	
	  	loop invariant loop_index_bounds: index <= loop_index <= index + n ;
		loop invariant linked: linked_n(sd, array, loop_index, n - loop_index, NULL);
		loop invariant result_is_min: \forall integer j; 0 <= j < loop_index 
			==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j])); 
		loop assigns sd, loop_index; 
		loop variant index + n - loop_index; 
	*/
	while (sd && !cpumask_test_cpu(prev_cpu, sched_domain_span(sd))){ 
		//@ ghost Before: ; 
		//@ assert linked: linked_n(sd, array, index + loop_index, n - loop_index, NULL);
		//@ assert sd_not_null: sd != NULL; 

		//@ assert sd_immediately_notin_mask: !cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
		//@ assert arr_j_immediately_notin_mask: !cpumask_test_cpu(prev_cpu, sched_domain_span(array[loop_index])); 

		//@ assert sd_unchanged: sd == \at(sd, Before); 
		
		//@ assert sd_later_notin_mask: !cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
		sd = sd->parent; 
		//@ assert sd_could_null: sd == NULL || \valid(sd); 

		//@ ghost loop_index++; 

		//if sd_changed passes, the node separation is working well enough that sd and its parent are never the same
		//@ assert sd_changed: sd != \at(sd, Before); 

		//@ assert not_found_yet: \forall integer j; 0 <= j < loop_index ==> !cpumask_test_cpu(prev_cpu, sched_domain_span(array[j]));
	}
	// don't think it knows that there will always be a NULL at the end of the chain
	//@ assert final_cases: sd == NULL || cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
	return sd; 
}