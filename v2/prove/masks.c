#include "../globals.c"
#include "../macros.c"

/*@
   axiomatic schedule_cpumask {
   logic bool cpumask_test_cpu(int cpu, struct cpumask *m);
   }
*/

/*@
requires 0 <= cpu < small_cpumask_bits;
requires \valid_read(m);
requires \valid_read(m->bits+(0 .. small_cpumask_bits - 1));

assigns \nothing;

ensures \result <==> m->bits[cpu];
ensures \result == cpumask_test_cpu(cpu, m);
*/
bool cpumask_test_cpu(int cpu, struct cpumask *m);

unsigned int cpumask_first(const struct cpumask * srcp);

bool cpumask_empty(const struct cpumask * srcp);

bool cpumask_and(struct cpumask * dstp, const struct cpumask * src1p, const struct cpumask * src2p);