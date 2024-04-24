#include "../defs.c"
#include "../globals.c"
#include "masks.c"



// to be minimum, need that there is never an sd that they've already hit that passes cpumask_test_cpu
// use ghost code as an index to subtract from the distance?

/*
requires INT_MIN <= prev_cpu <= INT_MAX; // can CPUs be negative? 

// requires separated and valid_read for all array members
// requires size of the array == size of the list using sd_distance

// requires each item in the list to map to the next in the array... but how do we say that? 

// note: they're not indexed - might need to use the linked_n inductive after all, but that opens up the can of worms with using the lemmas to help

assigns *sd;

// syntax : 

behavior above:
	// assumes exists an integer j st cpumask_test_cpu(prev_cpu, sched_domain_span(arr[j]))
	// ensures forall integer j below one returned, !cpumask_test_cpu(prev_cpu, sched_domain_span(arr[j]))
	// ensures cpumask_test_cpu(prev_cpu, sched_domain_span(\result); 

  assumes \exists integer j; offset <= j < size && addr[j];
  ensures offset <= \result < size;
  ensures addr[\result];
  ensures \forall integer j; offset <= j < \result ==> !addr[j];
  ensures \result < size;

behavior nowhere:
  assumes sd;
  ensures \result == size;

\\ keep: 
complete behaviors;
disjoint behaviors;
*/
struct sched_domain* testing_loop_1(struct sched_domain* sd, int prev_cpu) /*@ ghost (struct sched_domain arr[]) */{
									
	/*	
		loop invariant for all i jusqu'au j 
		loop assigns sd; 
		loop variant ;
	*/
	while (sd && !cpumask_test_cpu(prev_cpu, sched_domain_span(sd)))
			sd = sd->parent;
	return sd; 
}

