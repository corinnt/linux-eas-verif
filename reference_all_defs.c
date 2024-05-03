#define perf_domain_span(pd) NULL

#define this_rq()		this_cpu_ptr(&runqueues)

#define rcu_dereference(p) rcu_dereference_check(p, 0)

#define this_cpu_ptr(ptr) raw_cpu_ptr(ptr)

#define raw_cpu_ptr(ptr)						\
({									\
	__verify_pcpu_ptr(ptr);						\
	arch_raw_cpu_ptr(ptr);						\
})

#define __percpu_arg(x)		__percpu_prefix "%" 

#define arch_raw_cpu_ptr(ptr)				\
({							\
	unsigned long tcp_ptr__;			\
	asm ("add " __percpu_arg(1) ", %0"		\
	     : "=r" (tcp_ptr__)				\
	     : "m" (this_cpu_off), "0" (ptr));		\
	(typeof(*(ptr)) __kernel __force *)tcp_ptr__;	\
})

#define __percpu_prefix		"%%"__stringify(__percpu_seg)":"

#define __percpu_seg		gs

#define this_cpu_cpumask_var_ptr(x) this_cpu_ptr(x)

#define cpu_online_mask   ((const struct cpumask *)&__cpu_online_mask)

#define __stringify(x...)	__stringify_1(x)

#define __stringify_1(x...)	#x

#define ULONG_MAX	(~0UL)

/*  // moved to for_loops
#define for_each_cpu(cpu, mask)				\
	for_each_set_bit(cpu, cpumask_bits(mask), small_cpumask_bits)

#define for_each_set_bit(bit, addr, size) \
	for ((bit) = 0; (bit) = find_next_bit((addr), (size), (bit)), (bit) < (size); (bit)++)
*/

#define small_cpumask_bits ((unsigned int)NR_CPUS)

#define cpumask_bits(maskp) ((maskp)->bits)

#define NR_CPUS		CONFIG_NR_CPUS

#define CONFIG_NR_CPUS 64

#define lsub_positive(_ptr, _val) do {				\
	typeof(_ptr) ptr = (_ptr);				\
	*ptr -= min_t(typeof(*ptr), *ptr, _val);		\
} while (0)

#define min_t(type, x, y)	__careful_cmp((type)(x), (type)(y), <)

#define min(x, y)	__careful_cmp(x, y, <)

#define cpu_rq(cpu)		(&per_cpu(runqueues, (cpu)))

#define per_cpu_offset(x) (__per_cpu_offset[x])

#define per_cpu(var, cpu)	(*per_cpu_ptr(&(var), cpu))

#define per_cpu_ptr(ptr, cpu)						\
({									\
	__verify_pcpu_ptr(ptr);						\
	SHIFT_PERCPU_PTR((ptr), per_cpu_offset((cpu)));			\
})

#define SHIFT_PERCPU_PTR(__p, __offset)					\
	RELOC_HIDE((typeof(*(__p)) __kernel __force *)(__p), (__offset))

#define __verify_pcpu_ptr(ptr)						\
do {									\
	const void __percpu *__vpp_verify = (typeof((ptr) + 0))NULL;	\
	(void)__vpp_verify;						\
} while (0)

#define RELOC_HIDE(ptr, off)					\
  ({ unsigned long __ptr;					\
     __ptr = (unsigned long) (ptr);				\
    (typeof(ptr)) (__ptr + (off)); })

#define NULL ((void *)0)

#define __percpu	BTF_TYPE_TAG(percpu)

#define max(x, y)	__careful_cmp(x, y, >)

#define __careful_cmp(x, y, op) \
	__builtin_choose_expr(__safe_cmp(x, y), \
		__cmp(x, y, op), \
		__cmp_once(x, y, __UNIQUE_ID(__x), __UNIQUE_ID(__y), op))

#define __cmp_once(x, y, unique_x, unique_y, op) ({	\
		typeof(x) unique_x = (x);		\
		typeof(y) unique_y = (y);		\
		__cmp(unique_x, unique_y, op); })

#define __cmp(x, y, op)	((x) op (y) ? (x) : (y))

#define __safe_cmp(x, y) \
		(__typecheck(x, y) && __no_side_effects(x, y))

#define __no_side_effects(x, y) \
		(__is_constexpr(x) && __is_constexpr(y))

#define __typecheck(x, y) \
	(!!(sizeof((typeof(x) *)1 == (typeof(y) *)1)))

#define __is_constexpr(x) \
	(sizeof(int) == sizeof(*(8 ? ((void *)((long)(x) * 0l)) : (int *)8)))

#define rcu_dereference_check(p, c) \
	__rcu_dereference_check((p), __UNIQUE_ID(rcu), \
				(c) || rcu_read_lock_held(), __rcu)

#define __rcu_dereference_check(p, local, c, space) \
({ \
	/* Dependency order vs. p above. */ \
	typeof(*p) *local = (typeof(*p) *__force)READ_ONCE(p); \
	RCU_LOCKDEP_WARN(!(c), "suspicious rcu_dereference_check() usage"); \
	rcu_check_sparse(p, space); \
	((typeof(*p) __force __kernel *)(local)); \
})

#define rcu_check_sparse(p, space)

#define RCU_LOCKDEP_WARN(c, s) do { } while (0 && (c))

#define READ_ONCE(x)							\
({									\
	compiletime_assert_rwonce_type(x);				\
	__READ_ONCE(x);							\
})

#define __UNIQUE_ID(prefix) __PASTE(__PASTE(__UNIQUE_ID_, prefix), __COUNTER__)

#define __PASTE(a,b) ___PASTE(a,b)

#define ___PASTE(a,b) a##b

#define __force

#define __rcu		BTF_TYPE_TAG(rcu)

#define __kernel

#define BTF_TYPE_TAG(value)

#define __READ_ONCE(x)	(*(const volatile __unqual_scalar_typeof(x) *)&(x))

#define compiletime_assert_rwonce_type(t)					\
	compiletime_assert(__native_word(t) || sizeof(t) == sizeof(long long),	\
		"Unsupported access size for {READ,WRITE}_ONCE().")

#define compiletime_assert(condition, msg) \
	_compiletime_assert(condition, msg, __compiletime_assert_, __COUNTER__)

#define _compiletime_assert(condition, msg, prefix, suffix) \
	__compiletime_assert(condition, msg, prefix, suffix)

#define __compiletime_assert(condition, msg, prefix, suffix)		\
	do {								\
		/*							\
		 * __noreturn is needed to give the compiler enough	\
		 * information to avoid certain possibly-uninitialized	\
		 * warnings (regardless of the build failing).		\
		 */							\
		__noreturn extern void prefix ## suffix(void)		\
			__compiletime_error(msg);			\
		if (!(condition))					\
			prefix ## suffix();				\
	} while (0)

#define __native_word(t) \
	(sizeof(t) == sizeof(char) || sizeof(t) == sizeof(short) || \
	 sizeof(t) == sizeof(int) || sizeof(t) == sizeof(long))

#define __unqual_scalar_typeof(x) typeof(				\
		_Generic((x),						\
			 char:	(char)0,				\
			 __scalar_type_to_expr_cases(char),		\
			 __scalar_type_to_expr_cases(short),		\
			 __scalar_type_to_expr_cases(int),		\
			 __scalar_type_to_expr_cases(long),		\
			 __scalar_type_to_expr_cases(long long),	\
			 default: (x)))

#define __scalar_type_to_expr_cases(type)				\
		unsigned type:	(unsigned type)0,			\
		signed type:	(signed type)0

#define __noreturn                      __attribute__((__noreturn__))

#define __compiletime_error(msg)       __attribute__((__error__(msg)))

enum {false = 0,true = 1};
enum {__SCHED_FEAT_PLACE_LAG = 0,
	__SCHED_FEAT_PLACE_DEADLINE_INITIAL = 1,
	__SCHED_FEAT_RUN_TO_PARITY = 2,
	__SCHED_FEAT_NEXT_BUDDY = 3,
	__SCHED_FEAT_CACHE_HOT_BUDDY = 4,
	__SCHED_FEAT_WAKEUP_PREEMPTION = 5,
	__SCHED_FEAT_HRTICK = 6,
	__SCHED_FEAT_HRTICK_DL = 7,
	__SCHED_FEAT_DOUBLE_TICK = 8,
	__SCHED_FEAT_NONTASK_CAPACITY = 9,
	__SCHED_FEAT_TTWU_QUEUE = 10,
	__SCHED_FEAT_SIS_PROP = 11,
	__SCHED_FEAT_SIS_UTIL = 12,
	__SCHED_FEAT_WARN_DOUBLE_CLOCK = 13,
	__SCHED_FEAT_RT_PUSH_IPI = 14,
	__SCHED_FEAT_RT_RUNTIME_SHARE = 15,
	__SCHED_FEAT_LB_MIN = 16,
	__SCHED_FEAT_ATTACH_AGE_LOAD = 17,
	__SCHED_FEAT_WA_IDLE = 18,
	__SCHED_FEAT_WA_WEIGHT = 19,
	__SCHED_FEAT_WA_BIAS = 20,
	__SCHED_FEAT_UTIL_EST = 21,
	__SCHED_FEAT_UTIL_EST_FASTUP = 22,
	__SCHED_FEAT_LATENCY_WARN = 23,
	__SCHED_FEAT_HZ_BW = 24,
	__SCHED_FEAT_NR = 25};
	
struct sched_domain;
struct sched_domain;
struct perf_domain;
struct rq;
struct sched_domain;
struct root_domain;
struct cpumask;
struct rq;
struct energy_env;
struct perf_domain;
struct em_perf_domain;
struct cpumask;
struct cfs_rq;
struct rq;
struct task_struct;
struct sched_entity;

struct  util_est {
	unsigned int enqueued;
};

struct  sched_avg {
	unsigned long runnable_avg;
	unsigned long util_avg;
	struct  util_est util_est;
};

struct  cpumask {
	unsigned long bits[1];
};

typedef struct  cpumask cpumask_t;

struct  cfs_rq {
	struct  sched_avg avg;
};
struct  sched_entity {
//This empty struct was a problem for Frama-C
};

typedef unsigned long long __u64;

struct  energy_env {
	unsigned long task_busy_time;
	unsigned long pd_busy_time;
	unsigned long cpu_cap;
	unsigned long pd_cap;
};

struct  rq {
	struct  cfs_rq cfs;
	struct  root_domain *rd;
	unsigned long cpu_capacity;
};

struct  sched_domain {
	struct  sched_domain *parent;
	unsigned long span[];
};

typedef struct  cpumask cpumask_var_t[1];

struct  root_domain{
	int overutilized;
	struct  perf_domain *pd; 
};

struct  task_struct {
	int on_rq;
	struct  sched_entity se;
	cpumask_t *cpus_ptr;
};

enum cpu_util_type {
	FREQUENCY_UTIL = 0,
	ENERGY_UTIL = 1
};

typedef __u64 u64;
typedef _Bool bool;

enum uclamp_id { 
	UCLAMP_MIN = 0,
	UCLAMP_MAX = 1,
	UCLAMP_CNT = 2
};

struct  perf_domain {
	struct  em_perf_domain *em_pd;
	struct  perf_domain *next;
};
struct  cpumask __cpu_online_mask;

struct  sched_domain *sd_asym_cpucapacity;

unsigned long this_cpu_off;

cpumask_var_t select_rq_mask;

// POSSBUG do we need this? doesn't appear elsewhere
unsigned int sysctl_sched_features = (1UL << __SCHED_FEAT_PLACE_LAG) * true | (1UL << __SCHED_FEAT_PLACE_DEADLINE_INITIAL) * true | (1UL << __SCHED_FEAT_RUN_TO_PARITY) * true | (1UL << __SCHED_FEAT_NEXT_BUDDY) * false | (1UL << __SCHED_FEAT_CACHE_HOT_BUDDY) * true | (1UL << __SCHED_FEAT_WAKEUP_PREEMPTION) * true | (1UL << __SCHED_FEAT_HRTICK) * false | (1UL << __SCHED_FEAT_HRTICK_DL) * false | (1UL << __SCHED_FEAT_DOUBLE_TICK) * false | (1UL << __SCHED_FEAT_NONTASK_CAPACITY) * true | (1UL << __SCHED_FEAT_TTWU_QUEUE) * true | (1UL << __SCHED_FEAT_SIS_PROP) * false | (1UL << __SCHED_FEAT_SIS_UTIL) * true | (1UL << __SCHED_FEAT_WARN_DOUBLE_CLOCK) * false | (1UL << __SCHED_FEAT_RT_PUSH_IPI) * true | (1UL << __SCHED_FEAT_RT_RUNTIME_SHARE) * false | (1UL << __SCHED_FEAT_LB_MIN) * false | (1UL << __SCHED_FEAT_ATTACH_AGE_LOAD) * true | (1UL << __SCHED_FEAT_WA_IDLE) * true | (1UL << __SCHED_FEAT_WA_WEIGHT) * true | (1UL << __SCHED_FEAT_WA_BIAS) * true | (1UL << __SCHED_FEAT_UTIL_EST) * true | (1UL << __SCHED_FEAT_UTIL_EST_FASTUP) * true | (1UL << __SCHED_FEAT_LATENCY_WARN) * false | (1UL << __SCHED_FEAT_HZ_BW) * true | 0;

unsigned long __per_cpu_offset[64];
struct rq runqueues;

/* ----------- begin preds -------------- */

bool uclamp_is_used();

void rcu_read_unlock(); //TODO why is the IDE upset

int util_fits_cpu(unsigned long util, unsigned long uclamp_min, unsigned long uclamp_max, int cpu);

unsigned long uclamp_rq_get(struct rq * rq, enum uclamp_id clamp_id);

int rcu_read_lock_held();

void rcu_read_lock();

unsigned long uclamp_eff_value(struct task_struct * p, enum uclamp_id clamp_id);


/* ----------- end  preds -------------- */


/* ----------- begin helpers -------------- */

bool uclamp_rq_is_idle(struct rq * rq);

unsigned long uclamp_task_util(struct task_struct * p, unsigned long uclamp_min, unsigned long uclamp_max);

void sync_entity_load_avg(struct sched_entity * se);

struct cpumask * sched_domain_span(struct sched_domain * sd);

/* ----------- end helpers -------------- */

//TODO: maybe a pred? or maybe has some calc
void eenv_task_busy_time(struct energy_env * eenv, struct task_struct * p, int prev_cpu);

// for loops ?
unsigned long find_next_bit(const unsigned long * addr, unsigned long size, unsigned long offset);

void eenv_pd_busy_time(struct energy_env * eenv, struct cpumask * pd_cpus, struct task_struct * p);

/*--------- start masks.c ------------- */

bool cpumask_test_cpu(int cpu, const struct cpumask * cpumask);

unsigned int cpumask_first(const struct cpumask * srcp);

bool cpumask_empty(const struct cpumask * srcp);

bool cpumask_and(struct cpumask * dstp, const struct cpumask * src1p, const struct cpumask * src2p);

/*--------- end masks.c ------------- */

/*--------- start preds ------------- */

unsigned long cpu_util(int cpu, struct task_struct * p, int dst_cpu, int boost);

unsigned long compute_energy(struct energy_env * eenv, struct perf_domain * pd, struct cpumask * pd_cpus, struct task_struct * p, int dst_cpu);

unsigned long capacity_of(int cpu);

unsigned long arch_scale_thermal_pressure(int cpu);

unsigned long arch_scale_cpu_capacity(int cpu);

void __compiletime_assert_1068();

void __compiletime_assert_1066();

void __compiletime_assert_1065();
/*--------- end preds ------------- */

static int find_energy_efficient_cpu(struct task_struct *p, int prev_cpu)
{
	struct cpumask *cpus = this_cpu_cpumask_var_ptr(select_rq_mask);
	unsigned long prev_delta = ULONG_MAX, best_delta = ULONG_MAX;
	unsigned long p_util_min = uclamp_is_used() ? uclamp_eff_value(p, UCLAMP_MIN) : 0;
	unsigned long p_util_max = uclamp_is_used() ? uclamp_eff_value(p, UCLAMP_MAX) : 1024;
	struct root_domain *rd = this_rq()->rd;
	int cpu, best_energy_cpu, target = -1;
	int prev_fits = -1, best_fits = -1;
	unsigned long best_thermal_cap = 0;
	unsigned long prev_thermal_cap = 0;
	struct sched_domain *sd;
	struct perf_domain *pd;
	struct energy_env eenv;

	rcu_read_lock();
	pd = rcu_dereference(rd->pd); // of 
	if (!pd || READ_ONCE(rd->overutilized))
		goto unlock;

	/*
	 * Energy-aware wake-up happens on the lowest sched_domain starting
	 * from sd_asym_cpucapacity spanning over this_cpu and prev_cpu.
	 */
	sd = rcu_dereference(*this_cpu_ptr(&sd_asym_cpucapacity));
	while (sd && !cpumask_test_cpu(prev_cpu, sched_domain_span(sd)))
		sd = sd->parent;
	if (!sd) 
		goto unlock;

	target = prev_cpu;

	sync_entity_load_avg(&p->se);
	if (!uclamp_task_util(p, p_util_min, p_util_max))
		goto unlock;

	eenv_task_busy_time(&eenv, p, prev_cpu);

	for (; pd; pd = pd->next) {
		unsigned long util_min = p_util_min, util_max = p_util_max;
		unsigned long cpu_cap, cpu_thermal_cap, util;
		unsigned long cur_delta, max_spare_cap = 0;
		unsigned long rq_util_min, rq_util_max;
		unsigned long prev_spare_cap = 0;
		int max_spare_cap_cpu = -1;
		unsigned long base_energy;
		int fits, max_fits = -1;

		cpumask_and(cpus, perf_domain_span(pd), cpu_online_mask);

		if (cpumask_empty(cpus))
			continue;

		/* Account thermal pressure for the energy estimation */
		cpu = cpumask_first(cpus);
		cpu_thermal_cap = arch_scale_cpu_capacity(cpu);
		cpu_thermal_cap -= arch_scale_thermal_pressure(cpu);

		eenv.cpu_cap = cpu_thermal_cap;
		eenv.pd_cap = 0;

		for_each_cpu(cpu, cpus) {
			struct rq *rq = cpu_rq(cpu);

			eenv.pd_cap += cpu_thermal_cap;

			if (!cpumask_test_cpu(cpu, sched_domain_span(sd)))
				continue;

			if (!cpumask_test_cpu(cpu, p->cpus_ptr))
				continue;

			util = cpu_util(cpu, p, cpu, 0);
			cpu_cap = capacity_of(cpu);

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

			fits = util_fits_cpu(util, util_min, util_max, cpu);
			if (!fits)
				continue;

			lsub_positive(&cpu_cap, util);

			if (cpu == prev_cpu) {
				/* Always use prev_cpu as a candidate. */
				prev_spare_cap = cpu_cap;
				prev_fits = fits;
			} else if ((fits > max_fits) ||
				   ((fits == max_fits) && (cpu_cap > max_spare_cap))) {
				/*
				 * Find the CPU with the maximum spare capacity
				 * among the remaining CPUs in the performance
				 * domain.
				 */
				max_spare_cap = cpu_cap;
				max_spare_cap_cpu = cpu;
				max_fits = fits;
			}
		}

		if (max_spare_cap_cpu < 0 && prev_spare_cap == 0)
			continue;

		eenv_pd_busy_time(&eenv, cpus, p);
		/* Compute the 'base' energy of the pd, without @p */
		base_energy = compute_energy(&eenv, pd, cpus, p, -1);

		/* Evaluate the energy impact of using prev_cpu. */
		if (prev_spare_cap > 0) {
			prev_delta = compute_energy(&eenv, pd, cpus, p,
						    prev_cpu);
			/* CPU utilization has changed */
			if (prev_delta < base_energy)
				goto unlock;
			prev_delta -= base_energy;
			prev_thermal_cap = cpu_thermal_cap;
			best_delta = min(best_delta, prev_delta);
		}

		/* Evaluate the energy impact of using max_spare_cap_cpu. */
		if (max_spare_cap_cpu >= 0 && max_spare_cap > prev_spare_cap) {
			/* Current best energy cpu fits better */
			if (max_fits < best_fits)
				continue;

			/*
			 * Both don't fit performance hint (i.e. uclamp_min)
			 * but best energy cpu has better capacity.
			 */
			if ((max_fits < 0) &&
			    (cpu_thermal_cap <= best_thermal_cap))
				continue;

			cur_delta = compute_energy(&eenv, pd, cpus, p,
						   max_spare_cap_cpu);
			/* CPU utilization has changed */
			if (cur_delta < base_energy)
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

	if ((best_fits > prev_fits) ||
	    ((best_fits > 0) && (best_delta < prev_delta)) ||
	    ((best_fits < 0) && (best_thermal_cap > prev_thermal_cap)))
		target = best_energy_cpu;

	return target;

unlock:
	rcu_read_unlock();

	return target;
}
