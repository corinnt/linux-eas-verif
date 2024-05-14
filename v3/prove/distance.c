#include "../globals.c"

// use these functions to prove that loops will terminate
// can we subtract from these by having an index in the loop? or should it return a distance

// is this how we make the fn useable? don't think you necessarily need to
// this is a REGULAR comment rn: 
/* 
   axiomatic distance {
    logic unsigned sd_distance(struct sched_domain* sd);
    logic unsigned pd_distance(struct sched_domain* sd);
   }
*/

unsigned int sd_distance(struct sched_domain* sd) {
    unsigned int distance = 0; 
    while (sd){
        distance++;
        sd = sd->parent;
    } 
    return distance; 
}

unsigned int pd_distance(struct perf_domain* pd) {
    unsigned int distance = 0; 
    while (pd){
        distance++;
        pd = pd->next;
    } 
    return distance; 
}