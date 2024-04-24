#include "../globals.c"

/*@
requires 0 <= cpu < small_cpumask_bits;
assigns \nothing;
ensures \result <==> m->bits[cpu];
*/
bool cpumask_test_cpu(int cpu, struct cpumask *m);
// this one commented below was what was extracted - does it matter that it's const? 
// is dropping the const an artifact of the extraction?
//bool cpumask_test_cpu(int cpu, const struct cpumask * cpumask);

unsigned int cpumask_first(const struct cpumask * srcp);

bool cpumask_empty(const struct cpumask * srcp);

bool cpumask_and(struct cpumask * dstp, const struct cpumask * src1p, const struct cpumask * src2p);