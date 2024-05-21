#ifndef GLOBALS
#define GLOBALS
#include <stdbool.h>
#include <limits.h>

struct  util_est{
    unsigned int enqueued;
};

struct  sched_avg {
    unsigned long runnable_avg;
    unsigned long util_avg;
    struct  util_est util_est;
};

struct  cpumask {
    //unsigned long bits[1];
    unsigned long* bits; //manual replacement per Julia's recommendation
};

typedef struct  cpumask cpumask_t;

struct cfs_rq {
    struct  sched_avg avg;
};

struct  sched_entity {  // all fields removed - do we need them? added a filler
    unsigned long corinn_filler; 
};

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
    /*
	 * Span of all CPUs in this domain.
	 *
	 * NOTE: this field is variable length. (Allocated dynamically
	 * by attaching extra space to the end of the structure,
	 * depending on how many CPUs the kernel has booted up with)
	 */
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

//typedef __u64 u64;
//typedef _Bool bool;

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

unsigned long __per_cpu_offset[64];
struct rq runqueues;

#endif