
#include "../macros.c"
#include "../globals.c"
#include "../preds.c"
#include "masks.c"

// unsigned long p_util_min = uclamp_is_used() ? uclamp_eff_value(p, UCLAMP_MIN) : 0;
// unsigned long p_util_max = uclamp_is_used() ? uclamp_eff_value(p, UCLAMP_MAX) : 1024;

/*
// NOTES / TODOs
add thermal cap / contents from before entering loop
    make cpumask_and and cpumask_empty predicates / actual proofs 

invariants on loop about CPUs in mask which are eliminated earlier

prove lsub_positive
*/

/*@
    requires 0 <= cpu <= small_cpumask_bits && 0 <= prev_cpu <= small_cpumask_bits;


*/
void isolated_loop_2(int cpu, 
                     int prev_cpu,
                     int prev_fits,
                    struct cpumask* cpus, 
                    struct perf_domain* pd, 
                    struct energy_env eenv, // ig this isn't a pointer bc we're just dealing with it locally ?
                    unsigned long p_util_min, 
                    unsigned long p_util_max) {
    
    unsigned long util_min = p_util_min, util_max = p_util_max;
    unsigned long cpu_cap, cpu_thermal_cap, util;
    long prev_spare_cap = -1, max_spare_cap = -1;
    unsigned long rq_util_min, rq_util_max;
    //unsigned long cur_delta, base_energy;
    int max_spare_cap_cpu = -1;
    int fits, max_fits = -1;

    // excluding this info for now 

    /*
    //TODO predicate for cpumask_and - should be able to use cpumask_andnot
    cpumask_and(cpus, perf_domain_span(pd), cpu_online_mask);

    if (cpumask_empty(cpus)) //next loop iter if the pd doesn't have any CPUs online
    //  continue;
        return; 

    // Account thermal pressure for the enery estimation 
    cpu = cpumask_first(cpus); // this is just an optimization to skip zeros - eventually the prereq would be that there's nothing before in the mask
    cpu_thermal_cap = arch_scale_cpu_capacity(cpu); // provides arch-specific capacity info for the CPUs of that pd
    cpu_thermal_cap -= arch_scale_thermal_pressure(cpu); //maybe in include/linux/sched/topology.h 281?

    eenv.cpu_cap = cpu_thermal_cap;
    eenv.pd_cap = 0;
    */


    /* // this is from should_we_balance/smasks::is_core_idle
        loop invariant 0 <= i <= small_cpumask_bits;
        loop invariant \forall integer j; 0 <= j < i ==> cpu_smt_mask(cpu)->bits[j] ==> idle_cpu(j);
        loop assigns i;
        loop variant small_cpumask_bits - i;
    */

    // will eventually want more invariants: 
    //      the cpus are online, 
    //      that they never go below the "cpumask_first"

    // how do loop assigns work again? is it *anything* assiged?
    // how do we refer to the past CPUs to make the max invariants? can we index into `cpus`?

    /*@ 
        loop invariant 0 <= cpu <= small_cpumask_bits;
        loop invariant \forall integer j; 0 <= j < i ==> cpu_smt_mask(cpu)->bits[j] ==> idle_cpu(j);
        loop invariant \forall integer c; \old{cpu} <= 

        loop assigns cpu, 
                    eenv.pd_cap, 
                    util, 
                    cpu_cap, 
                    rq_util_min, rq_util_max, 
                    util_min, util_max; 
        loop variant small_cpumask_bits - cpu;
    */
    for_each_cpu(cpu, cpus) { // for each cpu in online cpus of pd
        struct rq *rq = cpu_rq(cpu);

        eenv.pd_cap += cpu_thermal_cap;

        if (!cpumask_test_cpu(cpu, sched_domain_span(sd))) 
            continue; // next loop iter if the cpu (from the pd) isn't also in the sched_domain

        if (!cpumask_test_cpu(cpu, p->cpus_ptr))
            continue; // TODO next loop iter if the cpu isn't in the process's cpus_ptr ?

        util = cpu_util(cpu, p, cpu, 0); // util = how much p needs. 0 is for no boosting. //TODO check the no boosting
        cpu_cap = capacity_of(cpu);      // what the cpu will fit

        /*
            * Skip CPUs that cannot satisfy the capacity request.
            * IOW, placing the task there would make the CPU
            * overutilized. Take uclamp into account to see how
            * much capacity we can get out of the CPU; this is
            * aligned with sched_cpu_util().
            */
        if (uclamp_is_used() && !uclamp_rq_is_idle(rq)) { //has clamping and the rq is busy
            /*
                * Open code uclamp_rq_util_with() except for
                * the clamp() part. Ie: apply max aggregation
                * only. util_fits_cpu() logic requires to
                * operate on non clamped util but must use the
                * max-aggregated uclamp_{min, max}.
                */
            rq_util_min = uclamp_rq_get(rq, UCLAMP_MIN);
            rq_util_max = uclamp_rq_get(rq, UCLAMP_MAX);

            util_min = max(rq_util_min, p_util_min);
            util_max = max(rq_util_max, p_util_max);
        }

        fits = util_fits_cpu(util, util_min, util_max, cpu); // find true/false will it fit
        //if (!fits) // skip all cpus that won't fit the task
        //    continue;

        lsub_positive(&cpu_cap, util); //local sub_positive

        if (cpu == prev_cpu) {
            /* Always use prev_cpu as a candidate. */
            prev_spare_cap = cpu_cap; //basically caching the vals for this pd
            prev_fits = fits;
        // Location of patched bug!! 
        } else if ((fits > max_fits) || // this is the best cpu so far
                ((fits == max_fits) && ((long)cpu_cap > max_spare_cap))) { 
            /*
                * Find the CPU with the maximum spare capacity
                * among the remaining CPUs in the performance
                * domain.
            */
            max_spare_cap = cpu_cap;
            max_spare_cap_cpu = cpu;
            max_fits = fits;
        }
    } // end CPU loop
}