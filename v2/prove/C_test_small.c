
#include "../macros.c"
#include "../globals.c"
#include "../preds.c"
#include "masks.c"

//this all proves

/*@
requires 0 <= prev_cpu < small_cpumask_bits; 
requires \valid_read(sd); 

assigns \result;

behavior in_mask:
    assumes sched_domain_span(sd)->bits[prev_cpu]; 
    ensures is_true: \result; 

behavior notin_mask: 
    assumes !sched_domain_span(sd)->bits[prev_cpu]; 									
	ensures is_false: !\result;

complete behaviors;
disjoint behaviors;
*/
bool testing_if_statement(struct sched_domain* sd, int prev_cpu){
    //@ assert sd_not_null: sd != NULL;
    if (cpumask_test_cpu(prev_cpu, sched_domain_span(sd))) {
        // assert sd_in_mask: cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
        //@ assert sd_in_mask: sched_domain_span(sd)->bits[prev_cpu]; 
        return true; 
    } else if (!cpumask_test_cpu(prev_cpu, sched_domain_span(sd))) { // just to make explicit the three cases
        // assert sd_notin_mask: !cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
        //@ assert sd_notin_mask: !sched_domain_span(sd)->bits[prev_cpu]; 
        return false; 
    }
}