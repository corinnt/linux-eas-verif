typedef _Bool bool;

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

struct  util_est{
    unsigned int enqueued;
};

struct  sched_avg{
    unsigned long runnable_avg;
    unsigned long util_avg;
    struct  util_est util_est;
};

struct  cpumask {
    unsigned long bits[1];
};

typedef struct  cpumask cpumask_t;

struct cfs_rq {
    struct  sched_avg avg;
};

struct  sched_entity { };

typedef unsigned long long __u64;

struct  energy_env {
    unsigned long task_busy_time;
    unsigned long pd_busy_time;
    unsigned long cpu_cap;
    unsigned long pd_cap;
};

struct rq {
    struct  cfs_rq cfs;
    struct  root_domain *rd;
    unsigned long cpu_capacity;
};

struct  sched_domain {
    struct  sched_domain *parent;
    unsigned long span[];
};

typedef struct  cpumask cpumask_var_t[1];

struct  root_domain {
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

struct  sched_domain *sd_asym_cpucapacity; // TODO(corinn) what's this notation?

unsigned long this_cpu_off;
cpumask_var_t select_rq_mask;
//unsigned int sysctl_sched_features = (1UL << __SCHED_FEAT_PLACE_LAG) * true | (1UL << __SCHED_FEAT_PLACE_DEADLINE_INITIAL) * true | (1UL << __SCHED_FEAT_RUN_TO_PARITY) * true | (1UL << __SCHED_FEAT_NEXT_BUDDY) * false | (1UL << __SCHED_FEAT_CACHE_HOT_BUDDY) * true | (1UL << __SCHED_FEAT_WAKEUP_PREEMPTION) * true | (1UL << __SCHED_FEAT_HRTICK) * false | (1UL << __SCHED_FEAT_HRTICK_DL) * false | (1UL << __SCHED_FEAT_DOUBLE_TICK) * false | (1UL << __SCHED_FEAT_NONTASK_CAPACITY) * true | (1UL << __SCHED_FEAT_TTWU_QUEUE) * true | (1UL << __SCHED_FEAT_SIS_PROP) * false | (1UL << __SCHED_FEAT_SIS_UTIL) * true | (1UL << __SCHED_FEAT_WARN_DOUBLE_CLOCK) * false | (1UL << __SCHED_FEAT_RT_PUSH_IPI) * true | (1UL << __SCHED_FEAT_RT_RUNTIME_SHARE) * false | (1UL << __SCHED_FEAT_LB_MIN) * false | (1UL << __SCHED_FEAT_ATTACH_AGE_LOAD) * true | (1UL << __SCHED_FEAT_WA_IDLE) * true | (1UL << __SCHED_FEAT_WA_WEIGHT) * true | (1UL << __SCHED_FEAT_WA_BIAS) * true | (1UL << __SCHED_FEAT_UTIL_EST) * true | (1UL << __SCHED_FEAT_UTIL_EST_FASTUP) * true | (1UL << __SCHED_FEAT_LATENCY_WARN) * false | (1UL << __SCHED_FEAT_HZ_BW) * true | 0;
unsigned int sysctl_sched_features =
    (1UL << __SCHED_FEAT_PLACE_LAG) * true |
    (1UL << __SCHED_FEAT_PLACE_DEADLINE_INITIAL) * true |
    (1UL << __SCHED_FEAT_RUN_TO_PARITY) * true |
    (1UL << __SCHED_FEAT_NEXT_BUDDY) * false |
    (1UL << __SCHED_FEAT_CACHE_HOT_BUDDY) * true |
    (1UL << __SCHED_FEAT_WAKEUP_PREEMPTION) * true |
    (1UL << __SCHED_FEAT_HRTICK) * false |
    (1UL << __SCHED_FEAT_HRTICK_DL) * false |
    (1UL << __SCHED_FEAT_DOUBLE_TICK) * false |
    (1UL << __SCHED_FEAT_NONTASK_CAPACITY) * true |
    (1UL << __SCHED_FEAT_TTWU_QUEUE) * true |
    (1UL << __SCHED_FEAT_SIS_PROP) * false |
    (1UL << __SCHED_FEAT_SIS_UTIL) * true |
    (1UL << __SCHED_FEAT_WARN_DOUBLE_CLOCK) * false |
    (1UL << __SCHED_FEAT_RT_PUSH_IPI) * true |
    (1UL << __SCHED_FEAT_RT_RUNTIME_SHARE) * false |
    (1UL << __SCHED_FEAT_LB_MIN) * false |
    (1UL << __SCHED_FEAT_ATTACH_AGE_LOAD) * true |
    (1UL << __SCHED_FEAT_WA_IDLE) * true |
    (1UL << __SCHED_FEAT_WA_WEIGHT) * true |
    (1UL << __SCHED_FEAT_WA_BIAS) * true |
    (1UL << __SCHED_FEAT_UTIL_EST) * true |
    (1UL << __SCHED_FEAT_UTIL_EST_FASTUP) * true |
    (1UL << __SCHED_FEAT_LATENCY_WARN) * false |
    (1UL << __SCHED_FEAT_HZ_BW) * true |
    0;

unsigned long __per_cpu_offset[64];
struct rq runqueues;


/*@
*/
#define this_cpu_cpumask_var_ptr(x) this_cpu_ptr(x)

/*@
*/
bool uclamp_is_used();

/*@
*/
unsigned long uclamp_eff_value(struct task_struct * p, enum uclamp_id clamp_id);

#define this_rq()		this_cpu_ptr(&runqueues)

void rcu_read_lock();

/*@
*/
#define rcu_dereference(p) rcu_dereference_check(p, 0)

#define READ_ONCE(x)							\
({									\
	compiletime_assert_rwonce_type(x);				\
	__READ_ONCE(x);							\
})

#define this_cpu_ptr(ptr) raw_cpu_ptr(ptr)

/*--------------------- begin find-sd loop ------------------------------*/

// Copied this over from should_we_balance
/*@
requires 0 <= cpu < small_cpumask_bits;
assigns \nothing;
ensures \result <==> m->bits[cpu];
*/
bool cpumask_test_cpu(int cpu, const struct cpumask * cpumask);

// TODO notation again
struct cpumask * sched_domain_span(struct sched_domain * sd);

// TODO prove or predicate?
void sync_entity_load_avg(struct sched_entity * se);

// TODO prove or predicate?
void eenv_task_busy_time(struct energy_env * eenv, struct task_struct * p, int prev_cpu);

/*--------------------- begin pd loop ------------------------------*/

// TODO copy over / adjust from should_we_balance
bool cpumask_and(struct cpumask * dstp, const struct cpumask * src1p, const struct cpumask * src2p);

#define perf_domain_span(pd) NULL

#define cpu_online_mask   ((const struct cpumask *)&__cpu_online_mask)

// TODO copy over / adjust from should_we_balance
bool cpumask_empty(const struct cpumask * srcp);

// TODO copy over / adjust from should_we_balance
unsigned int cpumask_first(const struct cpumask * srcp);

/*@
*/
unsigned long arch_scale_cpu_capacity(int cpu);

/*@
*/
unsigned long arch_scale_thermal_pressure(int cpu);

/*--------------------- begin cpu loop ------------------------------*/

// TODO copy over / adjust from should_we_balance
#define for_each_cpu(cpu, mask)				\
	for_each_set_bit(cpu, cpumask_bits(mask), small_cpumask_bits)

#define for_each_set_bit(bit, addr, size) \
	for ((bit) = 0; (bit) = find_next_bit((addr), (size), (bit)), (bit) < (size); (bit)++)

#define cpu_rq(cpu)		(&per_cpu(runqueues, (cpu)))



void rcu_read_unlock();
