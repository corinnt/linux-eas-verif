
#define perf_domain_span(pd) NULL

#define this_rq()		this_cpu_ptr(&runqueues)

#define rcu_dereference(p) rcu_dereference_check(p, 0)

#define this_cpu_ptr(ptr) raw_cpu_ptr(ptr)

#define raw_cpu_ptr(ptr)						\
({									\
	__verify_pcpu_ptr(ptr);						\
	arch_raw_cpu_ptr(ptr);						\
})

#define __percpu_arg(x)		__percpu_prefix "%" #x

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

// #define ULONG_MAX	(~0UL) //don't need to redefine from limits.h

/* 
// begin ~ moved to for_loops,c ~ 

#define for_each_cpu(cpu, mask)				\
	for_each_set_bit(cpu, cpumask_bits(mask), small_cpumask_bits)

#define for_each_set_bit(bit, addr, size) \
	for ((bit) = 0; (bit) = find_next_bit((addr), (size), (bit)), (bit) < (size); (bit)++)
    
//end moved to for_loops 
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