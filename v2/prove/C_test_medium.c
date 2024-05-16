
#include "../macros.c"
#include "../globals.c"
#include "../preds.c"
#include "masks.c"

/*@
requires 0 <= prev_cpu < small_cpumask_bits; 

assigns \result;

behavior in_mask:
	assumes sd != NULL; 
    assumes cpumask_test_cpu(prev_cpu, sched_domain_span(sd));  										
    ensures result_zero: \result == 0; 

behavior notin_mask: 
    assumes sd != NULL; 
    assumes !cpumask_test_cpu(prev_cpu, sched_domain_span(sd));  										
	ensures result_one: \result == 1;

behavior null: 
	assumes sd == NULL; 
	ensures result_two: \result == 2; 

complete behaviors;
disjoint behaviors;
*/
int testing_if_statement(struct sched_domain* sd, int prev_cpu){
    if (sd && cpumask_test_cpu(prev_cpu, sched_domain_span(sd))) {
        //@ assert sd_not_null1: sd != NULL; //def needs to not be null, but what if it does still pass?
        //@ assert sd_in_mask: cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
        return 0; 
    } else if (sd && !cpumask_test_cpu(prev_cpu, sched_domain_span(sd))) { // just to make explicit the three cases
        //@ assert sd_not_null2: sd != NULL; 
        //@ assert sd_notin_mask: !cpumask_test_cpu(prev_cpu, sched_domain_span(sd)); 
        return 1; 
    } else { // this is just if sd is null
        //@ assert sd_is_null: sd == NULL; 
        return 2; 
    }
}