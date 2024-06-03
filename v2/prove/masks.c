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


/*@
requires r1: context_ok;
requires r2: dstp == (void *)0 || \valid(dstp);
requires r3: \separated(dstp, &small_cpumask_bits, &nr_cpus, &this_cpu);
requires r5: \separated(src2p, &small_cpumask_bits, &nr_cpus, &this_cpu);

requires r7: \valid_read(src2p);

requires r11: \separated(dstp, src2p);
*/
bool cpumask_and(struct cpumask * dstp, 
                  const struct cpumask * src1p,
                  const struct cpumask * src2p) 
{
   return bitmap_and(cpumask_bits(dstp), cpumask_bits(src1p),
				       cpumask_bits(src2p), small_cpumask_bits);
}



// from should_we_balance5 : 

/*
requires r1: context_ok;
requires r2: dstp == (void *)0 || \valid(dstp);
requires r3: \separated(dstp, &small_cpumask_bits, &nr_cpus, &this_cpu);
requires r5: \separated(src2p, &small_cpumask_bits, &nr_cpus, &this_cpu);

requires r7: \valid_read(src2p);

requires r11: \separated(dstp, src2p);

requires
	  \forall integer i; \forall integer j; 0 <= i < small_cpumask_bits ==> 0 <= j < small_cpumask_bits ==>
	    \separated(&should_we_balance_tmpmask[j],
             sched_group_cpus(&sched_group_data),
             sched_group_mask(&sched_group_data),
             group_balance_mask(&sched_group_data),
             cpu_smt_mask(i));

ensures dstp == (void *)0 || (\valid_read(&dstp->bits) && \valid(dstp->bits+(0..small_cpumask_bits-1)));

  assigns *(dstp->bits+(0..small_cpumask_bits-1));

behavior empty_dst:
  assumes dstp == (void *)0;
  ensures !\result;

behavior nonempty_dst2:
  assumes dstp != (void *)0;
  assumes dstp != src2p;
  ensures \result;
  ensures \forall integer i; 0 <= i < small_cpumask_bits ==> (dstp->bits[i] <==> \at(dstp->bits[i] && !src2p->bits[i],Pre));
  ensures \forall integer i; 0 <= i < small_cpumask_bits ==> (src2p->bits[i] <==> \at(src2p->bits[i], Pre));

disjoint behaviors;
*/
static inline bool cpumask_andnot(struct cpumask *dstp,
				  const struct cpumask *src2p) {
  int i;
  if (!dstp)
    return false;
  /*@
  loop invariant 0 <= i <= small_cpumask_bits;
  loop invariant \forall integer j; 0 <= j < i ==> (dstp->bits[j] <==> \at(dstp->bits[j] && !src2p->bits[j],Pre));
  loop invariant \forall integer j; i <= j < small_cpumask_bits ==> (dstp->bits[j] <==> \at(dstp->bits[j],Pre));
  loop invariant \forall integer j; i <= j < small_cpumask_bits ==> (src2p->bits[j] <==> \at(src2p->bits[j],Pre));
  loop invariant dstp != src2p ==> \forall integer j; 0 <= j < i ==> (src2p->bits[j] <==> \at(src2p->bits[j],Pre));
  loop assigns i;
  loop assigns *(dstp->bits+(0..small_cpumask_bits-1));
  loop variant small_cpumask_bits - i;
  */
  for (i = 0; i != small_cpumask_bits; i++) {
    dstp->bits[i] = dstp->bits[i] && !src2p->bits[i];
  }
  return true;
}