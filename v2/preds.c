#include "macros.c"
#include "globals.c"

#include <stdbool.h>
#include <limits.h>

//this is just a fn that returns the sd->span of type as a cpumask
// don't think I need to be able to write to it, and don't think there are any particular limits
// TODO maybe need the span(array of unsigned longs) to be less than some max value?

/*@
   axiomatic spans_locks_and_archs {
    logic struct cpumask* sched_domain_span(struct sched_domain* sd);
   }
*/

//this is just a fn that returns the sd->span of type as a cpumask
// don't think I need to be able to write to it, and don't think there are any particular limits
// TODO maybe need the span(array of unsigned longs) to be less than some max value?
// don't particularly think so - it's just type coercion ig ? so any problems w the value would be way downstream

//TODO do I need to specify that sched_domain_span isn't null? like it shouldn't be, but we do pass NULL sd to it

/*@
assigns \nothing;
ensures \result == sched_domain_span(sd);
ensures \valid_read(\result); 
*/
struct cpumask * sched_domain_span(struct sched_domain * sd);

/* 
    \assigns nothing;
*/
int rcu_read_lock_held();

/* \requires

*/
void rcu_read_unlock();

unsigned long cpu_util(int cpu, struct task_struct * p, int dst_cpu, int boost);

unsigned long compute_energy(struct energy_env * eenv, 
                             struct perf_domain * pd, 
                             struct cpumask * pd_cpus, 
                             struct task_struct * p, 
                             int dst_cpu);

unsigned long capacity_of(int cpu);

unsigned long arch_scale_thermal_pressure(int cpu);

unsigned long arch_scale_cpu_capacity(int cpu);

void __compiletime_assert_1068();

void __compiletime_assert_1066();

void __compiletime_assert_1065();