#include "../globals.c"
#include "../macros.c"

/*@
   axiomatic schedule_cpumask {
   logic bool cpumask_test_cpu(int cpu, struct cpumask *m);
   }
*/

//QUESTION why does this not require valid_read ? 

/*
requires 0 <= cpu < small_cpumask_bits;
requires 
assigns \nothing;

behavior null: 
   assumes m == NULL; 
   ensures !\result;

behavior not_null:
   assumes m != NULL; 
   ensures \result ==> cpumask_test_cpu(cpu, m);

complete behaviors;
disjoint behaviors;
*/

/*@
requires 0 <= cpu < small_cpumask_bits;
requires \valid_read(m);

assigns \nothing;
ensures \result == cpumask_test_cpu(cpu, m);
*/
bool cpumask_test_cpu(int cpu, struct cpumask *m);
// the header commented below was what was extracted - does it matter that it's const? 
// is dropping the const an artifact of the extraction?
//bool cpumask_test_cpu(int cpu, const struct cpumask * cpumask);

unsigned int cpumask_first(const struct cpumask * srcp);

bool cpumask_empty(const struct cpumask * srcp);

bool cpumask_and(struct cpumask * dstp, const struct cpumask * src1p, const struct cpumask * src2p);