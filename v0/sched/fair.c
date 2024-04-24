#include <linux/energy_model.h>

#include "sched.h"


//fair.c 4777-4788
/*
 * Synchronize entity load avg of dequeued entity without locking
 * the previous rq.
 */
static void sync_entity_load_avg(struct sched_entity *se)
{
	struct cfs_rq *cfs_rq = cfs_rq_of(se);
	u64 last_update_time;

	last_update_time = cfs_rq_last_update_time(cfs_rq);
	__update_load_avg_blocked_se(last_update_time, se);
}

// fair.c: 7768 - 7776
/*
 * energy_env - Utilization landscape for energy estimation.
 * @task_busy_time: Utilization contribution by the task for which we test the
 *                  placement. Given by eenv_task_busy_time().
 * @pd_busy_time:   Utilization of the whole perf domain without the task
 *                  contribution. Given by eenv_pd_busy_time().
 * @cpu_cap:        Maximum CPU capacity for the perf domain.
 * @pd_cap:         Entire perf domain capacity. (pd->nr_cpus * cpu_cap).
 */
struct energy_env {
	unsigned long task_busy_time;
	unsigned long pd_busy_time;
	unsigned long cpu_cap;
	unsigned long pd_cap;
};

// fair.c: 7784-7802
/*
 * Compute the task busy time for compute_energy(). This time cannot be
 * injected directly into effective_cpu_util() because of the IRQ scaling.
 * The latter only makes sense with the most recent CPUs where the task has
 * run.
 */
static inline void eenv_task_busy_time(struct energy_env *eenv,
				       struct task_struct *p, int prev_cpu)
{
	unsigned long busy_time, max_cap = arch_scale_cpu_capacity(prev_cpu);
	unsigned long irq = cpu_util_irq(cpu_rq(prev_cpu));

	if (unlikely(irq >= max_cap))
		busy_time = max_cap;
	else
		busy_time = scale_irq_capacity(task_util_est(p), irq, max_cap);

	eenv->task_busy_time = busy_time;
}

/*
 * find_energy_efficient_cpu(): Find most energy-efficient target CPU for the
 * waking task. find_energy_efficient_cpu() looks for the CPU with maximum
 * spare capacity in each performance domain and uses it as a potential
 * candidate to execute the task. Then, it uses the Energy Model to figure
 * out which of the CPU candidates is the most energy-efficient.
 *
 * The rationale for this heuristic is as follows. In a performance domain,
 * all the most energy efficient CPU candidates (according to the Energy
 * Model) are those for which we'll request a low frequency. When there are
 * several CPUs for which the frequency request will be the same, we don't
 * have enough data to break the tie between them, because the Energy Model
 * only includes active power costs. With this model, if we assume that
 * frequency requests follow utilization (e.g. using schedutil), the CPU with
 * the maximum spare capacity in a performance domain is guaranteed to be among
 * the best candidates of the performance domain.
 *
 * In practice, it could be preferable from an energy standpoint to pack
 * small tasks on a CPU in order to let other CPUs go in deeper idle states,
 * but that could also hurt our chances to go cluster idle, and we have no
 * ways to tell with the current Energy Model if this is actually a good
 * idea or not. So, find_energy_efficient_cpu() basically favors
 * cluster-packing, and spreading inside a cluster. That should at least be
 * a good thing for latency, and this is consistent with the idea that most
 * of the energy savings of EAS come from the asymmetry of the system, and
 * not so much from breaking the tie between identical CPUs. That's also the
 * reason why EAS is enabled in the topology code only for systems where
 * SD_ASYM_CPUCAPACITY is set.
 *
 * NOTE: Forkees are not accepted in the energy-aware wake-up path because
 * they don't have any useful utilization data yet and it's not possible to
 * forecast their impact on energy consumption. Consequently, they will be
 * placed by find_idlest_cpu() on the least loaded CPU, which might turn out
 * to be energy-inefficient in some use-cases. The alternative would be to
 * bias new tasks towards specific types of CPUs first, or to try to infer
 * their util_avg from the parent task, but those heuristics could hurt
 * other use-cases too. So, until someone finds a better way to solve this,
 * let's keep things simple by re-using the existing slow path.
 */
static int find_energy_efficient_cpu(struct task_struct *p, int prev_cpu)
{
	/* Set up variables */
	//get original cpus as select_rq_mask
	struct cpumask *cpus = this_cpu_cpumask_var_ptr(select_rq_mask);
	unsigned long prev_delta = ULONG_MAX, best_delta = ULONG_MAX;
	// determine if we’re using utilization clamping
	unsigned long p_util_min = uclamp_is_used() ? uclamp_eff_value(p, UCLAMP_MIN) : 0;
	unsigned long p_util_max = uclamp_is_used() ? uclamp_eff_value(p, UCLAMP_MAX) : 1024;

	// get root_domain from this runqueue - is this then the entire system? no, its a subset
	struct root_domain *rd = this_rq()->rd;
	int cpu, best_energy_cpu, target = -1;
	int prev_fits = -1, best_fits = -1;
	unsigned long best_thermal_cap = 0;
	unsigned long prev_thermal_cap = 0;
	struct sched_domain *sd; 
	struct perf_domain *pd;
	struct energy_env eenv;

	rcu_read_lock();
	pd = rcu_dereference(rd->pd); // start with pd of root_domain (head of chain?)
	if (!pd || READ_ONCE(rd->overutilized)) //if no perf_domain for root_domain OR root_domain is overutilized
		goto unlock; 

	/* 
	 * Energy-aware wake-up happens on the lowest sched_domain starting
	 * from sd_asym_cpucapacity spanning over this_cpu and prev_cpu.
	 */

	//rcu_dereference = read copy update
	// SD_ASYM_CPUCAPACITY is sched_domain_flag indicating has different per cpu capacities
	// 		traverse up the tree to find lowest asymmetrical sd that contains the prev_cpu
	sd = rcu_dereference(*this_cpu_ptr(&sd_asym_cpucapacity)); // * original sd is lowest that has mixed topology *
	while (sd && !cpumask_test_cpu(prev_cpu, sched_domain_span(sd))) 
		sd = sd->parent;
	if (!sd) // there was no mixed topology ? 
		goto unlock;

	target = prev_cpu;

	sync_entity_load_avg(&p->se); 
	if (!task_util_est(p) && p_util_min == 0)
		goto unlock;

	eenv_task_busy_time(&eenv, p, prev_cpu); 

	// to do this loop invariant, need to specify the thing that diminishes as a function 
	// 		that returns the distance to the end of the pd chain
	for (; pd; pd = pd->next) {  //for each pd (in root_domain?)
		unsigned long util_min = p_util_min, util_max = p_util_max;
		unsigned long cpu_cap, cpu_thermal_cap, util;
		long prev_spare_cap = -1, max_spare_cap = -1;
		unsigned long rq_util_min, rq_util_max;
		unsigned long cur_delta, base_energy;
		int max_spare_cap_cpu = -1;
		int fits, max_fits = -1;

		cpumask_and(cpus, perf_domain_span(pd), cpu_online_mask);

		if (cpumask_empty(cpus)) //next loop iter if the pd doesn't have any CPUs online
			continue;

		/* Account thermal pressure for the energy estimation */
		cpu = cpumask_first(cpus);
		cpu_thermal_cap = arch_scale_cpu_capacity(cpu); // provides arch-specific capacity info for the CPUs of that pd
		cpu_thermal_cap -= arch_scale_thermal_pressure(cpu); //maybe in include/linux/sched/topology.h 281?

		eenv.cpu_cap = cpu_thermal_cap;
		eenv.pd_cap = 0;

		for_each_cpu(cpu, cpus) { // for each cpu in online cpus of pd
			struct rq *rq = cpu_rq(cpu);

			eenv.pd_cap += cpu_thermal_cap;

			if (!cpumask_test_cpu(cpu, sched_domain_span(sd))) 
				continue; // next loop iter if the cpu (from the pd) isn't also in the sched_domain

			if (!cpumask_test_cpu(cpu, p->cpus_ptr))
				continue; // TODO next loop iter if the cpu isn't in the process's cpus_ptr ?

			util = cpu_util(cpu, p, cpu, 0); // util = how much p needs
			cpu_cap = capacity_of(cpu);      // what the cpu will fit

			/*
			 * Skip CPUs that cannot satisfy the capacity request.
			 * IOW, placing the task there would make the CPU
			 * overutilized. Take uclamp into account to see how
			 * much capacity we can get out of the CPU; this is
			 * aligned with sched_cpu_util().
			 */
			if (uclamp_is_used() && !uclamp_rq_is_idle(rq)) {
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
			if (!fits) // skip all cpus that won't fit the proc
				continue;

			lsub_positive(&cpu_cap, util); //local sub_positive

			if (cpu == prev_cpu) {
				/* Always use prev_cpu as a candidate. */
				// corinn: how does this favoring logic work?
				prev_spare_cap = cpu_cap; //basically caching the vals for this pd
				prev_fits = fits;
			// Location of patched bug!! 
			} else if ((fits > max_fits) || // this is the best so far
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

		// what's the output from this cpu loop? 
		//	set prev_spare_cap IF prev is in pd
		//	set max_spare_cap, max_spare_cap_cpu, and max_fits for the pd
		
		if (max_spare_cap_cpu < 0 && prev_spare_cap < 0) //prev_spare_cap < 0 -> prev_cpu isn't in pd
			continue;

		eenv_pd_busy_time(&eenv, cpus, p);
		/* Compute the 'base' energy of the pd, without @p */
		base_energy = compute_energy(&eenv, pd, cpus, p, -1);

		/* Evaluate the energy impact of using prev_cpu. */
		if (prev_spare_cap > -1) { //prev_cpu was in this pd? and now prev_spare_cap is assigned
			prev_delta = compute_energy(&eenv, pd, cpus, p,
						    prev_cpu);
			/* CPU utilization has changed */
			if (prev_delta < base_energy)
				goto unlock;
			prev_delta -= base_energy;
			prev_thermal_cap = cpu_thermal_cap; //specific to pd
			best_delta = min(best_delta, prev_delta); //the best_delta stores the best change - might be from prev or 
		}

		/* Evaluate the energy impact of using max_spare_cap_cpu. */      // don't even bother if prev had more or same to spare
		if (max_spare_cap_cpu >= 0 && max_spare_cap > prev_spare_cap) {   // best_Delta was just assigned to running best or prev_delta
			/* Current best energy cpu fits better */
			if (max_fits < best_fits) //max doesn't fit, but already found a better from a diff pd
				continue;

			/*
			 * Both don't fit performance hint (i.e. uclamp_min)
			 * but best energy cpu has better capacity.
			 */
			if ((max_fits < 0) &&
			    (cpu_thermal_cap <= best_thermal_cap))
				continue;

			cur_delta = compute_energy(&eenv, pd, cpus, p, // is this the total if the process was added?
						   max_spare_cap_cpu);
			/* CPU utilization has changed */
			if (cur_delta < base_energy) // corinn: no locks held?
				goto unlock;
			cur_delta -= base_energy;

			/*
			 * Both fit for the task but best energy cpu has lower
			 * energy impact.
			 */
			if ((max_fits > 0) && (best_fits > 0) &&
			    (cur_delta >= best_delta))
				continue;

			best_delta = cur_delta;
			best_energy_cpu = max_spare_cap_cpu;
			best_fits = max_fits;
			best_thermal_cap = cpu_thermal_cap;
		}
	}
	rcu_read_unlock();

	//result of pd loop is best_delta, best_energy_cpu, best_fits, best_thermal_cap

	// final question:
	//	if best_fits, but prev doesn't
	//	if best_fits, and best_delta will use less energy than prev
	//	if best does not fit, but best has a better thermal cap than prev

	if ((best_fits > prev_fits) ||
	    ((best_fits > 0) && (best_delta < prev_delta)) ||
	    ((best_fits < 0) && (best_thermal_cap > prev_thermal_cap)))
		target = best_energy_cpu;

	return target;

unlock:
	rcu_read_unlock();

	return target;
}