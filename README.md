# Verification of Linux Energy-Aware Scheduling

Recently, power consumption-critical contexts, 
such as portable devices and high-performance computing, 
have increased demand for energy efficiency in OS process scheduling. Linux’s Completely Fair Scheduler (CFS) implements Energy Aware Scheduling,
which allows the scheduler to prioritize both performance and energy efficiency. 

When presented with candidate CPUs, 
the scheduler takes into account their capacities and their prospective energy consumptions 
to decide where to allocate the waking task. On heterogenous CPU topologies, 
this strategy has the potential to substantially reduce energy consumption 
without significantly harming throughput. However, scheduling algorithms are difficult to implement 
and almost impossible to check with testing alone. 

This work focuses on the formal verification 
of the energy-aware scheduling implementation in Linux’s CFS. By formalizing the behavior of this heuristic 
and verifying it using existing program verification tools such as Frama-C, 
we may ensure that this implementation adheres to its scheduling goals in all cases.

## Explanation of files

`v2/prove/C_isolated_loop1` contains a function with the first while-loop in the EAS function. All the contracts prove. 

`v2/prove/C_isolated_loop2` contains a function with the second while-loop in the EAS function. In progress. 

`find_eas_cpu` contains the full target function `find_energy_efficient_cpu`. 

`reference_all_defs` is the file extracted using Keisuke's tool containing all the macros and functions called in the function of interest. 


