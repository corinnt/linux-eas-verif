// copied from should_we_balance5/for_loops.c


#ifndef FORLOOPS
#define FORLOOPS
#include "../globals.c"



// ----------------------------------------------------------------------

// already in defs
//#define cpumask_bits(maskp) ((maskp)->bits)

// ----------------------------------------------------------------------

/*@
requires size <= INT_MAX;
requires \valid_read(addr + (0 .. size-1));
assigns \nothing;

behavior above:
  assumes \exists integer j; offset <= j < size && addr[j];
  ensures offset <= \result < size;
  ensures addr[\result];
  ensures \forall integer j; offset <= j < \result ==> !addr[j];
  ensures \result < size;

behavior nowhere:
  assumes \forall integer j; offset <= j < size ==> !addr[j];
  ensures \result == size;

complete behaviors;
disjoint behaviors;
*/
static int find_next_bit(const bool *addr, unsigned long size, unsigned long offset) {
	unsigned long i;
	/*@
	loop invariant offset <= i;
	loop invariant \forall integer j;
		offset <= j < i ==> !addr[j];
	loop assigns i;
	loop variant size-i;
	*/
	for (i=offset; i<size; i++)
		if (addr[i])
			return i;
	return size;
}

#define for_each_set_bit(bit, addr, size) \
	for ((bit) = 0; (bit) = find_next_bit((addr), (size), (bit)), (bit) < (size); (bit)++)

#define for_each_cpu(cpu, mask)				\
	for_each_set_bit(cpu, cpumask_bits(mask), small_cpumask_bits)

#endif