#include "../globals.c"
#include "../macros.c"

/* TODO this maybe needs to be proved/has logic 
*/
int util_fits_cpu(unsigned long util, unsigned long uclamp_min, unsigned long uclamp_max, int cpu);

// core_is_idle proved in should_we_balance
bool uclamp_rq_is_idle(struct rq * rq);

unsigned long uclamp_task_util(struct task_struct * p, unsigned long uclamp_min, unsigned long uclamp_max);

void sync_entity_load_avg(struct sched_entity * se);