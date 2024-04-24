#define PER_CPU_ATTRIBUTES

#define PER_CPU_BASE_SECTION ".data..percpu"

#define DECLARE_PER_CPU_READ_MOSTLY(type, name)			\
	DECLARE_PER_CPU_SECTION(type, name, "..read_mostly")

#define DECLARE_PER_CPU_SHARED_ALIGNED(type, name)			\
	DECLARE_PER_CPU_SECTION(type, name, PER_CPU_SHARED_ALIGNED_SECTION) \
	____cacheline_aligned_in_smp

#define DEFINE_PER_CPU(type, name)					\
	DEFINE_PER_CPU_SECTION(type, name, "")

#define DECLARE_PER_CPU(type, name)					\
	DECLARE_PER_CPU_SECTION(type, name, "")

#define DEFINE_PER_CPU_SECTION(type, name, sec)				\
	__PCPU_ATTRS(sec) __typeof__(type) name

#define DECLARE_PER_CPU_SECTION(type, name, sec)			\
	extern __PCPU_ATTRS(sec) __typeof__(type) name

#define __PCPU_ATTRS(sec)						\
	__percpu __attribute__((section(PER_CPU_BASE_SECTION sec)))	\
	PER_CPU_ATTRIBUTES

#define PER_CPU_SHARED_ALIGNED_SECTION "..shared_aligned"

#define __bitwise

#define HBP_NUM 4

#define GDT_ENTRY_TLS_ENTRIES		3

#define TS_COMM_LEN		32

#define randomized_struct_fields_end

#define randomized_struct_fields_start

#define RCU_NUM_LVLS	      2

#define ____cacheline_internodealigned_in_smp \
	__attribute__((__aligned__(1 << (INTERNODE_CACHE_SHIFT))))

#define INTERNODE_CACHE_SHIFT CONFIG_X86_INTERNODE_CACHE_SHIFT

#define CONFIG_X86_INTERNODE_CACHE_SHIFT 6

#define RLIM_NLIMITS		16

#define __SEQ_RT	IS_ENABLED(CONFIG_PREEMPT_RT)

#define SEQCOUNT_LOCKNAME(lockname, locktype, preemptible, lockmember, lockbase, lock_acquire) \
typedef struct seqcount_##lockname {					\
	seqcount_t		seqcount;				\
	__SEQ_LOCK(locktype	*lock);					\
} seqcount_##lockname##_t;						\
									\
static __always_inline seqcount_t *					\
__seqprop_##lockname##_ptr(seqcount_##lockname##_t *s)			\
{									\
	return &s->seqcount;						\
}									\
									\
static __always_inline unsigned						\
__seqprop_##lockname##_sequence(const seqcount_##lockname##_t *s)	\
{									\
	unsigned seq = READ_ONCE(s->seqcount.sequence);			\
									\
	if (!IS_ENABLED(CONFIG_PREEMPT_RT))				\
		return seq;						\
									\
	if (preemptible && unlikely(seq & 1)) {				\
		__SEQ_LOCK(lock_acquire);				\
		__SEQ_LOCK(lockbase##_unlock(s->lock));			\
									\
		/*							\
		 * Re-read the sequence counter since the (possibly	\
		 * preempted) writer made progress.			\
		 */							\
		seq = READ_ONCE(s->seqcount.sequence);			\
	}								\
									\
	return seq;							\
}									\
									\
static __always_inline bool						\
__seqprop_##lockname##_preemptible(const seqcount_##lockname##_t *s)	\
{									\
	if (!IS_ENABLED(CONFIG_PREEMPT_RT))				\
		return preemptible;					\
									\
	/* PREEMPT_RT relies on the above LOCK+UNLOCK */		\
	return false;							\
}									\
									\
static __always_inline void						\
__seqprop_##lockname##_assert(const seqcount_##lockname##_t *s)		\
{									\
	__SEQ_LOCK(lockdep_assert_held(lockmember));			\
}

#define __SEQ_LOCK(expr)

#define raw_spin_lock(lock)	_raw_spin_lock(lock)

#define RCU_CBLIST_NSEGS	4

#define MAXQUOTAS 3

#define CPUCLOCK_MAX		3

#define __module_memory_align ____cacheline_aligned

#define MODULE_NAME_LEN MAX_PARAM_PREFIX_LEN

#define MAX_PARAM_PREFIX_LEN (64 - sizeof(unsigned long))

#define Elf_Sym		Elf64_Sym

#define BINPRM_BUF_SIZE 256

#define UEVENT_BUFFER_SIZE		2048

#define UEVENT_NUM_ENVP			64

#define radix_tree_root		xarray

#define NR_FWNODE_REFERENCE_ARGS	8

#define __iomem

#define PAGE_SIZE		(_AC(1,UL) << PAGE_SHIFT)

#define PAGE_SHIFT		12

#define SB_FREEZE_LEVELS (SB_FREEZE_COMPLETE - 1)

#define __randomize_layout __designated_init

#define __designated_init

#define DNAME_INLINE_LEN 32

#define CPUPRI_NR_PRIORITIES	(MAX_RT_PRIO+1)

#define MAX_RT_PRIO		100

#define CPUIDLE_DESC_LEN	32

#define CPUIDLE_NAME_LEN	16

#define CPUIDLE_STATE_MAX	10

#define MAX_CGROUP_ROOT_NAMELEN 64

#define PATH_MAX        4096

#define NR_PSI_RESOURCES	0

#define MAX_CFTYPE_NAME		64

#define ACPI_ID_LEN	16

#define __private

#define UID_GID_MAP_MAX_BASE_EXTENTS 5

#define AT_VECTOR_SIZE (2*(AT_VECTOR_SIZE_ARCH + AT_VECTOR_SIZE_BASE + 1))

#define AT_VECTOR_SIZE_BASE 22

#define AT_VECTOR_SIZE_ARCH 3

#define USE_SPLIT_PMD_PTLOCKS	(USE_SPLIT_PTE_PTLOCKS && \
		IS_ENABLED(CONFIG_ARCH_ENABLE_SPLIT_PMD_PTLOCK))

#define USE_SPLIT_PTE_PTLOCKS	(NR_CPUS >= CONFIG_SPLIT_PTLOCK_CPUS)

#define ____cacheline_aligned_in_smp ____cacheline_aligned

#define CONFIG_ARCH_ENABLE_SPLIT_PMD_PTLOCK 1

#define CONFIG_SPLIT_PTLOCK_CPUS 4

#define USE_CMPXCHG_LOCKREF \
	(IS_ENABLED(CONFIG_ARCH_USE_CMPXCHG_LOCKREF) && \
	 IS_ENABLED(CONFIG_SMP) && SPINLOCK_SIZE <= 4)

#define SPINLOCK_SIZE 4

#define aligned_u64		__aligned_u64

#define __aligned_u64 __u64 __attribute__((aligned(8)))

#define IS_ENABLED(option) __or(IS_BUILTIN(option), IS_MODULE(option))

#define IS_MODULE(option) __is_defined(option##_MODULE)

#define IS_BUILTIN(option) __is_defined(option)

#define ____is_defined(arg1_or_junk)	__take_second_arg(arg1_or_junk 1, 0)

#define ___is_defined(val)		____is_defined(__ARG_PLACEHOLDER_##val)

#define __is_defined(x)			___is_defined(x)

#define ____or(arg1_or_junk, y)		__take_second_arg(arg1_or_junk 1, y)

#define ___or(x, y)			____or(__ARG_PLACEHOLDER_##x, y)

#define __or(x, y)			___or(x, y)

#define __take_second_arg(__ignored, val, ...) val

#define __ARG_PLACEHOLDER_1 0,

#define CONFIG_ARCH_USE_CMPXCHG_LOCKREF 1

#define CONFIG_SMP 1

#define __SIGINFO 			\
struct {				\
	int si_signo;			\
	int si_errno;			\
	int si_code;			\
	union __sifields _sifields;	\
}

#define rcu_head callback_head

#define ____cacheline_aligned __attribute__((__aligned__(SMP_CACHE_BYTES)))

#define SMP_CACHE_BYTES L1_CACHE_BYTES

#define L1_CACHE_BYTES	(1 << L1_CACHE_SHIFT)

#define L1_CACHE_SHIFT	(CONFIG_X86_L1_CACHE_SHIFT)

#define CONFIG_X86_L1_CACHE_SHIFT 6

#define HASH_LEN_DECLARE u32 hash; u32 len

#define pgoff_t unsigned long

#define DECLARE_FLEX_ARRAY(TYPE, NAME) \
	__DECLARE_FLEX_ARRAY(TYPE, NAME)

#define __DECLARE_FLEX_ARRAY(TYPE, NAME)	\
	struct { \
		struct { } __empty_ ## NAME; \
		TYPE NAME[]; \
	}

#define __ARCH_SI_BAND_T long

#define __ADDR_BND_PKEY_PAD  (__alignof__(void *) < sizeof(short) ? \
			      sizeof(short) : __alignof__(void *))

#define __ARCH_SI_CLOCK_T __kernel_clock_t

#define UUID_SIZE 16

#define MAX_NUMNODES    (1 << NODES_SHIFT)

#define NODES_SHIFT     CONFIG_NODES_SHIFT

#define BITS_TO_LONGS(nr)	__KERNEL_DIV_ROUND_UP(nr, BITS_PER_TYPE(long))

#define BITS_PER_TYPE(type)	(sizeof(type) * BITS_PER_BYTE)

#define BITS_PER_BYTE		8

#define DECLARE_BITMAP(name,bits) \
	unsigned long name[BITS_TO_LONGS(bits)]

#define __KERNEL_DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))

#define CONFIG_NODES_SHIFT 6

#define _NSIG_WORDS	(_NSIG / _NSIG_BPW)

#define _NSIG_BPW	64

#define _NSIG		64

#define __user	BTF_TYPE_TAG(user)

#define fits_capacity(cap, max)	((cap) * 1280 < (max) * 1024)

#define to_cpumask(bitmap)						\
	((struct cpumask *)(1 ? (bitmap)				\
			    : (void *)sizeof(__check_is_bitmap(bitmap))))

#define rcu_lock_release(a)		do { } while (0)

#define __release(x)	(void)0

#define rcu_lock_acquire(a)		do { } while (0)

#define __acquire(x)	(void)0

#define __ffs(word)				\
	(__builtin_constant_p(word) ?		\
	 (unsigned long)__builtin_ctzl(word) :	\
	 variable__ffs(word))

#define GENMASK(h, l) \
	(GENMASK_INPUT_CHECK(h, l) + __GENMASK(h, l))

#define __GENMASK(h, l) \
	(((~UL(0)) - (UL(1) << (l)) + 1) & \
	 (~UL(0) >> (BITS_PER_LONG - 1 - (h))))

#define GENMASK_INPUT_CHECK(h, l) \
	(BUILD_BUG_ON_ZERO(__builtin_choose_expr( \
		__is_constexpr((l) > (h)), (l) > (h), 0)))

#define BUILD_BUG_ON_ZERO(e) ((int)(sizeof(struct { int:(-!!(e)); })))

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

#define ULONG_MAX	(~0UL)

#define for_each_cpu(cpu, mask)				\
	for_each_set_bit(cpu, cpumask_bits(mask), small_cpumask_bits)

#define for_each_set_bit(bit, addr, size) \
	for ((bit) = 0; (bit) = find_next_bit((addr), (size), (bit)), (bit) < (size); (bit)++)

#define test_bit(nr, addr)		bitop(_test_bit, nr, addr)

#define bitop(op, nr, addr)						\
	((__builtin_constant_p(nr) &&					\
	  __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)NULL) &&	\
	  (uintptr_t)(addr) != (uintptr_t)NULL &&			\
	  __builtin_constant_p(*(const unsigned long *)(addr))) ?	\
	 const##op(nr, addr) : op(nr, addr))

#define small_cpumask_bits ((unsigned int)NR_CPUS)

#define cpumask_bits(maskp) ((maskp)->bits)

#define NR_CPUS		CONFIG_NR_CPUS

#define CONFIG_NR_CPUS 64

#define lsub_positive(_ptr, _val) do {				\
	typeof(_ptr) ptr = (_ptr);				\
	*ptr -= min_t(typeof(*ptr), *ptr, _val);		\
} while (0)

#define sched_feat(x) !!(sysctl_sched_features & (1UL << __SCHED_FEAT_##x))

#define current get_current()

#define min_t(type, x, y)	__careful_cmp((type)(x), (type)(y), <)

#define unlikely(x)	__builtin_expect(!!(x), 0)

#define UL(x)		(_UL(x))

#define _UL(x)		(_AC(x, UL))

#define _AC(X,Y)	__AC(X,Y)

#define __AC(X,Y)	(X##Y)

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

#define small_const_nbits(nbits) \
	(__builtin_constant_p(nbits) && (nbits) <= BITS_PER_LONG && (nbits) > 0)

#define SCHED_CAPACITY_SCALE		(1L << SCHED_CAPACITY_SHIFT)

#define SCHED_CAPACITY_SHIFT		SCHED_FIXEDPOINT_SHIFT

#define SCHED_FIXEDPOINT_SHIFT		10

#define BITS_PER_LONG 64

#define __always_inline                 inline __attribute__((__always_inline__))

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

#define notrace __attribute__((no_instrument_function))

#define __inline_maybe_unused __maybe_unused

#define inline inline __gnu_inline __inline_maybe_unused notrace

#define __maybe_unused                  __attribute__((__unused__))

#define __gnu_inline                    __attribute__((__gnu_inline__))

enum {TASK_COMM_LEN};
enum {SB_UNFROZEN,SB_FREEZE_WRITE,SB_FREEZE_PAGEFAULT,SB_FREEZE_FS,SB_FREEZE_COMPLETE};
enum {MM_FILEPAGES,MM_ANONPAGES,MM_SWAPENTS,MM_SHMEMPAGES,NR_MM_COUNTERS};
enum {false,true};
enum {__SCHED_FEAT_PLACE_LAG,__SCHED_FEAT_PLACE_DEADLINE_INITIAL,__SCHED_FEAT_RUN_TO_PARITY,__SCHED_FEAT_NEXT_BUDDY,__SCHED_FEAT_CACHE_HOT_BUDDY,__SCHED_FEAT_WAKEUP_PREEMPTION,__SCHED_FEAT_HRTICK,__SCHED_FEAT_HRTICK_DL,__SCHED_FEAT_DOUBLE_TICK,__SCHED_FEAT_NONTASK_CAPACITY,__SCHED_FEAT_TTWU_QUEUE,__SCHED_FEAT_SIS_PROP,__SCHED_FEAT_SIS_UTIL,__SCHED_FEAT_WARN_DOUBLE_CLOCK,__SCHED_FEAT_RT_PUSH_IPI,__SCHED_FEAT_RT_RUNTIME_SHARE,__SCHED_FEAT_LB_MIN,__SCHED_FEAT_ATTACH_AGE_LOAD,__SCHED_FEAT_WA_IDLE,__SCHED_FEAT_WA_WEIGHT,__SCHED_FEAT_WA_BIAS,__SCHED_FEAT_UTIL_EST,__SCHED_FEAT_UTIL_EST_FASTUP,__SCHED_FEAT_LATENCY_WARN,__SCHED_FEAT_HZ_BW,__SCHED_FEAT_NR};
struct xol_area;
struct workqueue_struct;
struct wakeup_source;
struct wake_q_node;
struct wake_irq;
struct wait_page_queue;
struct vma_lock;
struct vm_struct;
struct uts_namespace;
struct user_struct;
struct user_namespace;
struct uprobe_task;
struct uprobe;
struct uid_gid_extent;
struct ucounts;
struct tty_struct;
struct tty_audit_buf;
struct tracer;
struct tracepoint_func;
struct tracepoint;
struct trace_event_functions;
struct trace_event_fields;
struct trace_event_class;
struct trace_eval_map;
struct trace_entry;
struct trace_array;
struct time_namespace;
struct taskstats;
struct task_group;
struct task_delay_info;
struct static_key_mod;
struct static_call_site;
struct static_call_mod;
struct static_call_key;
struct srcu_usage;
struct srcu_struct;
struct srcu_data;
struct signal_struct;
struct sighand_struct;
struct sem_undo_list;
struct seccomp_filter;
struct sched_rt_entity;
struct sched_group_capacity;
struct sched_group;
struct sched_domain_shared;
struct sched_dl_entity;
struct rt_mutex_waiter;
struct rseq;
struct robust_list_head;
struct ring_buffer_iter;
struct rhlist_head;
struct rhash_head;
struct return_instance;
struct reclaim_state;
struct rcu_node;
struct rb_node;
struct quota_format_type;
struct psi_group;
struct property;
struct pollfd;
struct pm_subsys_data;
struct pid_namespace;
struct perf_raw_record;
struct perf_raw_frag;
struct perf_event_context;
struct perf_cpu_pmu_context;
struct perf_cgroup_info;
struct perf_cgroup;
struct perf_callchain_entry;
struct perf_buffer;
struct perf_branch_stack;
struct perf_addr_filter_range;
struct percpu_ref_data;
struct page_pool;
struct orc_entry;
struct old_timespec32;
struct nsproxy;
struct net;
struct nameidata;
struct mtd_info;
struct msi_device_data;
struct module_sect_attrs;
struct module_param_attrs;
struct module_notes_attrs;
struct mod_kallsyms;
struct mnt_namespace;
struct mmu_notifier_subscriptions;
struct mm_cid;
struct mem_cgroup;
struct math_emu_info;
struct llist_node;
struct list_lru_node;
struct linux_binfmt;
struct ldt_struct;
struct kset;
struct kmem_cache;
struct kioctx_table;
struct key_user;
struct key_type;
struct key_tag;
struct key_restriction;
struct kernfs_root;
struct kernfs_ops;
struct kernfs_open_node;
struct kernfs_node;
struct kernfs_iattrs;
struct kernel_param;
struct jump_entry;
struct irq_domain;
struct ipc_namespace;
struct iommu_group;
struct io_uring_task;
struct io_tlb_mem;
struct io_context;
struct io_bitmap;
struct hrtimer_cpu_base;
struct hrtimer_clock_base;
struct hlist_node;
struct hlist_head;
struct hlist_bl_node;
struct group_info;
struct gendisk;
struct futex_pi_state;
struct fsnotify_mark_connector;
struct fs_struct;
struct fs_pin;
struct freq_constraints;
struct fpstate;
struct files_struct;
struct file_ra_state;
struct file_lock_context;
struct fasync_struct;
struct exception_table_entry;
struct event_filter;
struct em_perf_state;
struct driver_private;
struct device_private;
struct device_physical_location;
struct device_node;
struct device_dma_parameters;
struct dev_pm_qos_request;
struct dev_pm_qos;
struct dev_pm_domain;
struct dev_iommu;
struct ctl_table_poll;
struct ctl_node;
struct ctl_dir;
struct cred;
struct cpuidle_state;
struct cpuidle_driver_kobj;
struct cpuidle_device_kobj;
struct cpudl_item;
struct cpu_stop_done;
struct core_thread;
struct core_state;
struct completion;
struct compat_robust_list_head;
struct cgroup_subsys;
struct cgroup_rstat_cpu;
struct cgroup_root;
struct cgroup_namespace;
struct cdev;
struct capture_control;
struct bug_entry;
struct bpf_prog_array;
struct blocking_notifier_head;
struct block_device;
struct blk_plug;
struct bio_list;
struct balance_callback;
struct backing_dev_info;
struct audit_context;
struct assoc_array_ptr;
struct array_buffer;
struct anon_vma;
struct __kernel_timespec;
struct xattr_handler;
struct vm_operations_struct;
struct vdso_image;
struct sysfs_ops;
struct super_operations;
struct seq_operations;
struct sched_class;
struct quotactl_ops;
struct proc_ns_operations;
struct of_device_id;
struct kset_uevent_ops;
struct kparam_string;
struct kparam_array;
struct kobj_type;
struct kernfs_ops;
struct kernel_symbol;
struct kernel_param_ops;
struct iommu_ops;
struct inode_operations;
struct fwnode_operations;
struct fs_parameter_spec;
struct file_operations;
struct file;
struct export_operations;
struct dquot_operations;
struct dma_map_ops;
struct device_type;
struct dev_pm_ops;
struct dev_pagemap_ops;
struct dentry_operations;
struct cred;
struct bus_type;
struct bus_dma_region;
struct attribute_group;
struct address_space_operations;
struct acpi_device_id;
struct work_struct;
struct timer_list;
struct affinity_context;
struct readahead_control;
struct perf_event_pmu_context;
struct pt_regs;
struct perf_sample_data;
struct mm_struct;
struct percpu_ref;
struct irq_work;
struct callback_head;
struct class;
struct vm_fault;
struct shrinker;
struct vfsmount;
struct path;
struct offset_ctx;
struct file_system_type;
struct inode;
struct ctl_table_root;
struct module_kobject;
struct module_attribute;
struct attribute;
struct pipe_inode_info;
struct shrink_control;
struct restart_block;
struct perf_output_handle;
struct wait_queue_entry;
struct mempolicy;
struct trace_event_call;
struct css_set;
struct swap_info_struct;
struct qc_state;
struct qc_dqblk;
struct kqid;
struct qc_info;
struct super_block;
struct seq_file;
struct rq_flags;
struct notifier_block;
struct module;
struct posix_acl;
struct iattr;
struct kstat;
struct mnt_idmap;
struct list_head;
struct linux_binprm;
struct iov_iter;
struct kiocb;
union key_payload;
struct key_type;
struct key;
struct io_comp_batch;
struct io_uring_cmd;
struct fiemap_extent_info;
struct fwnode_handle;
struct fs_context;
struct bin_attribute;
struct kobject;
struct file_lock;
struct dquot;
struct device_driver;
struct device;
struct dev_pagemap;
struct kstatfs;
struct fileattr;
struct ctl_table_set;
struct ctl_table_header;
struct ctl_table;
struct cpuidle_driver;
struct cpuidle_device;
struct coredump_params;
struct cgroup_taskset;
struct cftype;
struct writeback_control;
struct page;
struct path;
struct fwnode_endpoint;
struct fwnode_reference_args;
struct kobj_uevent_env;
struct qstr;
struct qstr;
struct dentry;
struct kernel_param;
struct trace_event;
struct trace_iterator;
struct hrtimer;
struct sock;
struct kobj_ns_type_operations;
struct vm_area_struct;
struct delayed_call;
struct kobject;
struct dentry;
struct device;
struct pmu;
struct dir_context;
struct folio;
struct address_space;
struct fwnode_handle;
struct kernfs_open_file;
struct poll_table_struct;
struct file;
struct srcu_node;
struct pid;
struct perf_event;
struct inode;
struct cpuidle_state_kobj;
struct cgroup_subsys_state;
struct cgroup;
struct quota_format_ops;
struct sched_domain;
struct sched_domain;
struct perf_domain;
struct rq;
struct sched_domain;
struct root_domain;
struct em_perf_domain;
struct cpumask;
struct rq;
struct energy_env;
struct perf_domain;
struct cpumask;
struct cfs_rq;
struct rq;
struct task_struct;
struct sched_entity;
typedef unsigned char __u8;
typedef unsigned short __u16;
typedef __u8 u8;
typedef __u16 u16;
typedef struct  {
int counter;} atomic_t;
struct  qspinlock{
union  {
atomic_t val;
struct  {
u8 locked;
u8 pending;} ;
struct  {
u16 locked_pending;
u16 tail;} ;} ;};
typedef long long __s64;
typedef unsigned long long __u64;
typedef unsigned int __u32;
typedef struct  qspinlock arch_spinlock_t;
typedef __s64 s64;
typedef __u64 u64;
typedef __u32 u32;
struct  raw_spinlock{
arch_spinlock_t raw_lock;};
typedef struct  {
s64 counter;} atomic64_t;
typedef atomic64_t atomic_long_t;
union  sigval{
int sival_int;
void *sival_ptr;};
typedef long __kernel_long_t;
struct  spinlock{
union  {
struct  raw_spinlock rlock;} ;};
struct  list_head{
struct  list_head *next;
struct  list_head *prev;};
struct  rb_node{
unsigned long __rb_parent_color;
struct  rb_node *rb_right;
struct  rb_node *rb_left;};
typedef s64 ktime_t;
typedef int __kernel_pid_t;
typedef unsigned int __kernel_uid32_t;
typedef int __kernel_timer_t;
typedef union  sigval sigval_t;
typedef __kernel_long_t __kernel_clock_t;
struct  fxregs_state{
u16 cwd;
u16 swd;
u16 twd;
u16 fop;
union  {
struct  {
u64 rip;
u64 rdp;} ;
struct  {
u32 fip;
u32 fcs;
u32 foo;
u32 fos;} ;} ;
u32 mxcsr;
u32 mxcsr_mask;
u32 st_space[20];
u32 xmm_space[20];
u32 padding[20];
union  {
u32 padding1[20];
u32 sw_reserved[20];} ;};
struct  xstate_header{
u64 xfeatures;
u64 xcomp_bv;
u64 reserved[8];};
typedef struct  spinlock spinlock_t;
struct  rb_root{
struct  rb_node *rb_node;};
typedef unsigned int __kernel_gid32_t;
enum hrtimer_restart{HRTIMER_NORESTART,HRTIMER_RESTART};
typedef struct  {
atomic_long_t a;} local_t;
typedef __kernel_uid32_t uid_t;
typedef __kernel_gid32_t gid_t;
typedef __kernel_uid32_t projid_t;
struct  callback_head{
struct  callback_head *next;
void (*func)(struct  callback_head*) ;};
struct  timerqueue_node{
struct  rb_node node;
ktime_t expires;};
struct  rhash_head{
struct  rhash_head *next;};
struct  fregs_state{
u32 cwd;
u32 swd;
u32 twd;
u32 fip;
u32 fcs;
u32 foo;
u32 fos;
u32 st_space[20];
u32 status;};
struct  swregs_state{
u32 cwd;
u32 swd;
u32 twd;
u32 fip;
u32 fcs;
u32 foo;
u32 fos;
u32 st_space[20];
u8 ftop;
u8 changed;
u8 lookahead;
u8 no_update;
u8 rm;
u8 alimit;
struct  math_emu_info *info;
u32 entry_eip;};
struct  xregs_state{
struct  fxregs_state i387;
struct  xstate_header header;
u8 extended_state_area[3];};
struct  wait_queue_head{
spinlock_t lock;
struct  list_head head;};
typedef void (*work_func_t)(struct  work_struct*) ;
struct  rb_root_cached{
struct  rb_root rb_root;
struct  rb_node *rb_leftmost;};
struct  seqcount{
unsigned int sequence;};
struct  cpumask{
unsigned long bits[1];};
typedef int __kernel_clockid_t;
struct  refcount_struct{
atomic_t refs;};
typedef struct  wait_queue_head wait_queue_head_t;
typedef int __s32;
struct  optimistic_spin_queue{
atomic_t tail;};
typedef struct  raw_spinlock raw_spinlock_t;
struct  hlist_node{
struct  hlist_node *next;
struct  hlist_node **pprev;};
typedef struct  seqcount seqcount_t;
struct  qrwlock{
union  {
atomic_t cnts;
struct  {
u8 wlocked;
u8 __lstate[3];} ;} ;
arch_spinlock_t wait_lock;};
typedef void (*__signalfn_t )(int) ;
typedef void (*__restorefn_t )() ;
struct  hlist_head{
struct  hlist_node *first;};
typedef unsigned long __kernel_ulong_t;
typedef struct  {
unsigned long val;} swp_entry_t;
struct  hw_perf_event_extra{
u64 config;
unsigned int reg;
int alloc;
int idx;};
struct  hrtimer{
struct  timerqueue_node node;
ktime_t _softexpires;
enum hrtimer_restart (*function)(struct  hrtimer*) ;
struct  hrtimer_clock_base *base;
u8 state;
u8 is_rel;
u8 is_soft;
u8 is_hard;};
struct  arch_hw_breakpoint{
unsigned long address;
unsigned long mask;
u8 len;
u8 type;};
struct  rhlist_head{
struct  rhash_head rhead;
struct  rhlist_head *next;};
typedef struct  {
local_t a;} local64_t;
typedef __kernel_clockid_t clockid_t;
enum timespec_type{TT_NONE,TT_NATIVE,TT_COMPAT};
union  __sifields{
struct  {
__kernel_pid_t _pid;
__kernel_uid32_t _uid;} _kill;
struct  {
__kernel_timer_t _tid;
int _overrun;
sigval_t _sigval;
int _sys_private;} _timer;
struct  {
__kernel_pid_t _pid;
__kernel_uid32_t _uid;
sigval_t _sigval;} _rt;
struct  {
__kernel_pid_t _pid;
__kernel_uid32_t _uid;
int _status;
__kernel_clock_t _utime;
__kernel_clock_t _stime;} _sigchld;
struct  {
void *_addr;
union  {
int _trapno;
short _addr_lsb;
struct  {
char _dummy_bnd[6];
void *_lower;
void *_upper;} _addr_bnd;
struct  {
char _dummy_pkey[6];
__u32 _pkey;} _addr_pkey;
struct  {
unsigned long _data;
__u32 _type;
__u32 _flags;} _perf;} ;} _sigfault;
struct  {
long _band;
int _fd;} _sigpoll;
struct  {
void *_call_addr;
int _syscall;
unsigned int _arch;} _sigsys;};
union  fpregs_state{
struct  fregs_state fsave;
struct  fxregs_state fxsave;
struct  swregs_state soft;
struct  xregs_state xsave;
u8 __padding[3];};
typedef struct  refcount_struct refcount_t;
typedef __u32 Elf64_Word;
typedef __u16 Elf64_Half;
typedef __u64 Elf64_Addr;
typedef __u64 Elf64_Xword;
typedef struct  {
} lockdep_map_p;
typedef unsigned long pgdval_t;
typedef __s32 s32;
typedef short __s16;
struct  work_struct{
atomic_long_t data;
struct  list_head entry;
work_func_t func;};
typedef unsigned long pteval_t;
typedef unsigned long pmdval_t;
struct  timerqueue_head{
struct  rb_root_cached rb_root;};
typedef struct  qrwlock arch_rwlock_t;
typedef __signalfn_t  __sighandler_t;
typedef __restorefn_t  __sigrestore_t;
typedef struct  {
unsigned long sig[1];} sigset_t;
typedef struct  {
uid_t val;} kuid_t;
typedef struct  {
gid_t val;} kgid_t;
typedef struct  {
projid_t val;} kprojid_t;
typedef struct  cpumask cpumask_var_t[1];
struct  uid_gid_extent{
u32 first;
u32 lower_first;
u32 count;};
typedef __kernel_ulong_t __kernel_size_t;
typedef long long __kernel_loff_t;
struct  latch_tree_node{
struct  rb_node node[2];};
struct  llist_node{
struct  llist_node *next;};
typedef long long qsize_t;
struct  rcu_sync{
int gp_state;
int gp_count;
wait_queue_head_t gp_wait;
struct  callback_head cb_head;};
struct  rcuwait{
struct  task_struct *task;};
struct  rw_semaphore{
atomic_long_t count;
atomic_long_t owner;
struct  optimistic_spin_queue osq;
raw_spinlock_t wait_lock;
struct  list_head wait_list;};
struct  mutex{
atomic_long_t owner;
raw_spinlock_t wait_lock;
struct  optimistic_spin_queue osq;
struct  list_head wait_list;};
typedef __s16 s16;
struct  timer_list{
struct  hlist_node entry;
unsigned long expires;
void (*function)(struct  timer_list*) ;
u32 flags;};
struct  range{
u64 start;
u64 end;};
typedef __kernel_long_t __kernel_ssize_t;
typedef unsigned long pudval_t;
struct  seqcount_spinlock{
seqcount_t seqcount;};
struct  ctl_table_header{
union  {
struct  {
struct  ctl_table *ctl_table;
int ctl_table_size;
int used;
int count;
int nreg;} ;
struct  callback_head rcu;} ;
struct  completion *unregistering;
struct  ctl_table *ctl_table_arg;
struct  ctl_table_root *root;
struct  ctl_table_set *set;
struct  ctl_dir *parent;
struct  ctl_node *node;
struct  hlist_head inodes;};
typedef __kernel_size_t size_t;
typedef __kernel_loff_t loff_t;
enum freq_qos_req_type{FREQ_QOS_MIN,FREQ_QOS_MAX};
struct  plist_node{
int prio;
struct  list_head prio_list;
struct  list_head node_list;};
struct  swait_queue_head{
raw_spinlock_t lock;
struct  list_head task_list;};
typedef unsigned int gfp_t;
struct  assoc_array{
struct  assoc_array_ptr *root;
unsigned long nr_leaves_on_tree;};
struct  arch_uprobe_task{
unsigned long saved_scratch_register;
unsigned int saved_trap_nr;
unsigned int saved_tf;};
struct  plist_head{
struct  list_head node_list;};
enum pm_qos_type{PM_QOS_UNITIALIZED,PM_QOS_MAX,PM_QOS_MIN};
struct  util_est{
unsigned int enqueued;
unsigned int ewma;};
struct  fpu_state_perm{
u64 __state_perm;
unsigned int __state_size;
unsigned int __user_state_size;};
struct  fpstate{
unsigned int size;
unsigned int user_size;
u64 xfeatures;
u64 user_xfeatures;
u64 xfd;
unsigned int is_valloc:1;
unsigned int is_guest:1;
unsigned int is_confidential:1;
unsigned int in_use:1;
union  fpregs_state regs;};
struct  kref{
refcount_t refcount;};
struct  elf64_sym{
Elf64_Word st_name;
unsigned char st_info;
unsigned char st_other;
Elf64_Half st_shndx;
Elf64_Addr st_value;
Elf64_Xword st_size;};
struct  seqcount_raw_spinlock{
seqcount_t seqcount;};
struct  percpu_ref{
unsigned long percpu_count_ptr;
struct  percpu_ref_data *data;};
struct  rcu_work{
struct  work_struct work;
struct  callback_head rcu;
struct  workqueue_struct *wq;};
struct  task_cputime{
u64 stime;
u64 utime;
unsigned long long sum_exec_runtime;};
typedef _Bool bool;
typedef __kernel_ssize_t ssize_t;
struct  posix_cputimer_base{
u64 nextevt;
struct  timerqueue_head tqhead;};
typedef struct  seqcount_spinlock seqcount_spinlock_t;
struct  sigaction{
__sighandler_t sa_handler;
unsigned long sa_flags;
__sigrestore_t sa_restorer;
sigset_t sa_mask;};
enum quota_type{USRQUOTA,GRPQUOTA,PRJQUOTA};
struct  cpupri_vec{
atomic_t count;
cpumask_var_t mask;};
struct  pm_message{
int event;};
typedef unsigned long pgprotval_t;
struct  desc_struct{
u16 limit0;
u16 base0;
u16 base1:8;
u16 type:4;
u16 s:1;
u16 dpl:2;
u16 p:1;
u16 limit1:4;
u16 avl:1;
u16 l:1;
u16 d:1;
u16 g:1;
u16 base2:8;};
struct  mod_tree_node{
struct  module *mod;
struct  latch_tree_node node;};
typedef struct  elf64_sym Elf64_Sym;
typedef int (*wait_queue_func_t)(struct  wait_queue_entry*,unsigned int,int,void*) ;
struct  __call_single_node{
struct  llist_node llist;
union  {
unsigned int u_flags;
atomic_t a_flags;} ;
u16 src;
u16 dst;};
typedef void (*smp_call_func_t)(void*) ;
struct  mem_dqinfo{
struct  quota_format_type *dqi_format;
int dqi_fmt_id;
struct  list_head dqi_dirty_list;
unsigned long dqi_flags;
unsigned int dqi_bgrace;
unsigned int dqi_igrace;
qsize_t dqi_max_spc_limit;
qsize_t dqi_max_ino_limit;
void *dqi_priv;};
struct  percpu_rw_semaphore{
struct  rcu_sync rss;
unsigned int *read_count;
struct  rcuwait writer;
wait_queue_head_t waiters;
atomic_t block;};
typedef struct  {
pgdval_t pgd;} pgd_t;
struct  percpu_counter{
raw_spinlock_t lock;
s64 count;
struct  list_head list;
s32 *counters;};
typedef struct  seqcount_raw_spinlock seqcount_raw_spinlock_t;
struct  cgroup_file{
struct  kernfs_node *kn;
unsigned long notified_at;
struct  timer_list notify_timer;};
typedef u64 blkcnt_t;
typedef unsigned long (*perf_copy_f)(void*,void*,unsigned long,unsigned long) ;
enum print_line_t{TRACE_TYPE_PARTIAL_LINE,TRACE_TYPE_HANDLED,TRACE_TYPE_UNHANDLED,TRACE_TYPE_NO_CONSUME};
typedef u64 sector_t;
typedef struct  {
pteval_t pte;} pte_t;
typedef struct  {
pmdval_t pmd;} pmd_t;
struct  task_cputime_atomic{
atomic64_t utime;
atomic64_t stime;
atomic64_t sum_exec_runtime;};
typedef struct  {
arch_rwlock_t raw_lock;} rwlock_t;
enum pid_type{PIDTYPE_PID,PIDTYPE_TGID,PIDTYPE_PGID,PIDTYPE_SID,PIDTYPE_MAX};
typedef unsigned short umode_t;
struct  ctl_dir{
struct  ctl_table_header header;
struct  rb_root root;};
struct  seq_buf{
char *buffer;
size_t size;
size_t len;
loff_t readpos;};
struct  kernfs_elem_dir{
unsigned long subdirs;
struct  rb_root children;
struct  kernfs_root *root;
unsigned long rev;};
struct  kernfs_elem_symlink{
struct  kernfs_node *target_kn;};
struct  kernfs_elem_attr{
struct  kernfs_ops *ops;
struct  kernfs_open_node *open;
loff_t size;
struct  kernfs_node *notify_next;};
struct  pm_qos_flags_request{
struct  list_head node;
s32 flags;};
struct  freq_qos_request{
enum freq_qos_req_type type;
struct  plist_node pnode;
struct  freq_constraints *qos;};
typedef __s64 time64_t;
struct  hlist_bl_node{
struct  hlist_bl_node *next;
struct  hlist_bl_node **pprev;};
enum dl_dev_state{DL_DEV_NO_DRIVER,DL_DEV_PROBING,DL_DEV_DRIVER_BOUND,DL_DEV_UNBINDING};
typedef struct  pm_message pm_message_t;
struct  completion{
unsigned int done;
struct  swait_queue_head wait;};
enum rpm_request{RPM_REQ_NONE,RPM_REQ_IDLE,RPM_REQ_SUSPEND,RPM_REQ_AUTOSUSPEND,RPM_REQ_RESUME};
enum rpm_status{RPM_INVALID,RPM_ACTIVE,RPM_RESUMING,RPM_SUSPENDED,RPM_SUSPENDING};
struct  xarray{
spinlock_t xa_lock;
gfp_t xa_flags;
void *xa_head;};
struct  keyring_index_key{
unsigned long hash;
union  {
struct  {
u16 desc_len;
char desc[6];} ;
unsigned long x;} ;
struct  key_type *type;
struct  key_tag *domain_tag;
char *description;};
union  key_payload{
void *rcu_data0;
void *data[4];};
struct  pm_qos_constraints{
struct  plist_head list;
s32 target_value;
s32 default_value;
s32 no_constraint_value;
enum pm_qos_type type;
struct  blocking_notifier_head *notifiers;};
struct  blocking_notifier_head{
struct  rw_semaphore rwsem;
struct  notifier_block *head;};
typedef u32 errseq_t;
typedef unsigned long vm_flags_t;
struct  page{
unsigned long flags;
union  {
struct  {
union  {
struct  list_head lru;
struct  {
void *__filler;
unsigned int mlock_count;} ;
struct  list_head buddy_list;
struct  list_head pcp_list;} ;
struct  address_space *mapping;
union  {
unsigned long index;
unsigned long share;} ;
unsigned long private;} ;
struct  {
unsigned long pp_magic;
struct  page_pool *pp;
unsigned long _pp_mapping_pad;
unsigned long dma_addr;
union  {
unsigned long dma_addr_upper;
atomic_long_t pp_frag_count;} ;} ;
struct  {
unsigned long compound_head;} ;
struct  {
struct  dev_pagemap *pgmap;
void *zone_device_data;} ;
struct  callback_head callback_head;} ;
union  {
atomic_t _mapcount;
unsigned int page_type;} ;
atomic_t _refcount;};
struct  sched_avg{
u64 last_update_time;
u64 load_sum;
u64 runnable_sum;
u32 util_sum;
u32 period_contrib;
unsigned long load_avg;
unsigned long runnable_avg;
unsigned long util_avg;
struct  util_est util_est;};
struct  load_weight{
unsigned long weight;
u32 inv_weight;};
struct  kernel_siginfo{
struct  {
int si_signo;
int si_errno;
int si_code;
union  __sifields _sifields;} ;};
struct  arch_tlbflush_unmap_batch{
struct  cpumask cpumask;};
struct  fpu{
unsigned int last_cpu;
unsigned long avx512_timestamp;
struct  fpstate *fpstate;
struct  fpstate *__task_fpstate;
struct  fpu_state_perm perm;
struct  fpu_state_perm guest_perm;
struct  fpstate __fpstate;};
struct  kobject{
char *name;
struct  list_head entry;
struct  kobject *parent;
struct  kset *kset;
struct  kobj_type *ktype;
struct  kernfs_node *sd;
struct  kref kref;
unsigned int state_initialized:1;
unsigned int state_in_sysfs:1;
unsigned int state_add_uevent_sent:1;
unsigned int state_remove_uevent_sent:1;
unsigned int uevent_suppress:1;};
struct  rt_prio_array{
unsigned long bitmap[1];
struct  list_head queue[100];};
typedef int (*cpu_stop_fn_t)(void*) ;
struct  maple_tree{
union  {
spinlock_t ma_lock;
lockdep_map_p ma_external_lock;} ;
unsigned int ma_flags;
void *ma_root;};
typedef struct  {
u64 ctx_id;
atomic64_t tlb_gen;
struct  rw_semaphore ldt_usr_sem;
struct  ldt_struct *ldt;
unsigned long flags;
struct  mutex lock;
void *vdso;
struct  vdso_image *vdso_image;
atomic_t perf_rdpmc_allowed;
u16 pkey_allocation_map;
s16 execute_only_pkey;} mm_context_t;
struct  uprobes_state{
struct  xol_area *xol_area;};
typedef struct  {
unsigned long bits[1];} nodemask_t;
struct  cgroup_subsys_state{
struct  cgroup *cgroup;
struct  cgroup_subsys *ss;
struct  percpu_ref refcnt;
struct  list_head sibling;
struct  list_head children;
struct  list_head rstat_css_node;
int id;
unsigned int flags;
u64 serial_nr;
atomic_t online_cnt;
struct  work_struct destroy_work;
struct  rcu_work destroy_rwork;
struct  cgroup_subsys_state *parent;};
enum cgroup_subsys_id{cpuset_cgrp_id,cpu_cgrp_id,cpuacct_cgrp_id,io_cgrp_id,devices_cgrp_id,freezer_cgrp_id,net_cls_cgrp_id,perf_event_cgrp_id,net_prio_cgrp_id,hugetlb_cgrp_id,pids_cgrp_id,rdma_cgrp_id,misc_cgrp_id,debug_cgrp_id,CGROUP_SUBSYS_COUNT};
struct  cgroup_base_stat{
struct  task_cputime cputime;};
struct  prev_cputime{
u64 utime;
u64 stime;
raw_spinlock_t lock;};
struct  cgroup_bpf{
};
struct  cgroup_freezer_state{
bool freeze;
int e_freeze;
int nr_frozen_descendants;
int nr_frozen_tasks;};
typedef struct  {
uid_t val;} vfsuid_t;
typedef struct  {
gid_t val;} vfsgid_t;
typedef u32 __kernel_dev_t;
enum migrate_mode{MIGRATE_ASYNC,MIGRATE_SYNC_LIGHT,MIGRATE_SYNC,MIGRATE_SYNC_NO_COPY};
typedef struct  {
pudval_t pud;} pud_t;
struct  cpu_itimer{
u64 expires;
u64 incr;};
struct  rlimit{
__kernel_ulong_t rlim_cur;
__kernel_ulong_t rlim_max;};
struct  k_sigaction{
struct  sigaction sa;};
struct  kqid{
union  {
kuid_t uid;
kgid_t gid;
kprojid_t projid;} ;
enum quota_type type;};
enum freeze_holder{FREEZE_HOLDER_KERNEL,FREEZE_HOLDER_USERSPACE};
struct  cpuidle_state{
char name[6];
char desc[6];
s64 exit_latency_ns;
s64 target_residency_ns;
unsigned int flags;
unsigned int exit_latency;
int power_usage;
unsigned int target_residency;
int (*enter)(struct  cpuidle_device*,struct  cpuidle_driver*,int) ;
int (*enter_dead)(struct  cpuidle_device*,int) ;
int (*enter_s2idle)(struct  cpuidle_device*,struct  cpuidle_driver*,int) ;};
typedef s32 int32_t;
typedef u32 uint32_t;
struct  upid{
int nr;
struct  pid_namespace *ns;};
struct  lock_class_key{
};
struct  pgprot{
pgprotval_t pgprot;};
typedef unsigned int __poll_t;
typedef struct  cpumask cpumask_t;
typedef struct  kernel_siginfo kernel_siginfo_t;
enum trace_reg{TRACE_REG_REGISTER,TRACE_REG_UNREGISTER,TRACE_REG_PERF_REGISTER,TRACE_REG_PERF_UNREGISTER,TRACE_REG_PERF_OPEN,TRACE_REG_PERF_CLOSE,TRACE_REG_PERF_ADD,TRACE_REG_PERF_DEL};
enum dev_dma_attr{DEV_DMA_NOT_SUPPORTED,DEV_DMA_NON_COHERENT,DEV_DMA_COHERENT};
typedef unsigned int vm_fault_t;
typedef void *fl_owner_t;
struct  module_memory{
void *base;
unsigned int size;
struct  mod_tree_node mtn;};
typedef int tracepoint_ptr_t;
struct  wait_queue_entry{
unsigned int flags;
void *private;
wait_queue_func_t func;
struct  list_head entry;};
typedef signed char __s8;
struct  cpuidle_state_usage{
unsigned long long disable;
unsigned long long usage;
u64 time_ns;
unsigned long long above;
unsigned long long below;
unsigned long long rejected;
unsigned long long s2idle_usage;
unsigned long long s2idle_time;};
struct  __call_single_data{
struct  __call_single_node node;
smp_call_func_t func;
void *info;};
struct  perf_branch_entry{
__u64 from;
__u64 to;
__u64 mispred:1;
__u64 predicted:1;
__u64 in_tx:1;
__u64 abort:1;
__u64 cycles:16;
__u64 type:4;
__u64 spec:2;
__u64 new_type:4;
__u64 priv:3;
__u64 reserved:31;};
struct  hrtimer_clock_base{
struct  hrtimer_cpu_base *cpu_base;
unsigned int index;
clockid_t clockid;
seqcount_raw_spinlock_t seq;
struct  hrtimer *running;
struct  timerqueue_head active;
ktime_t (*get_time)() ;
ktime_t offset;};
typedef __kernel_dev_t dev_t;
struct  qc_type_state{
unsigned int flags;
unsigned int spc_timelimit;
unsigned int ino_timelimit;
unsigned int rt_spc_timelimit;
unsigned int spc_warnlimit;
unsigned int ino_warnlimit;
unsigned int rt_spc_warnlimit;
unsigned long long ino;
blkcnt_t blocks;
blkcnt_t nextents;};
typedef int (*key_restrict_link_func_t)(struct  key*,struct  key_type*,union  key_payload*,struct  key*) ;
struct  perf_raw_frag{
union  {
struct  perf_raw_frag *next;
unsigned long pad;} ;
perf_copy_f copy;
void *data;
u32 size;};
typedef enum print_line_t (*trace_print_func)(struct  trace_iterator*,int,struct  trace_event*) ;
enum cpu_idle_type{CPU_IDLE,CPU_NOT_IDLE,CPU_NEWLY_IDLE,CPU_MAX_IDLE_TYPES};
struct  trace_event{
struct  hlist_node node;
int type;
struct  trace_event_functions *funcs;};
enum fault_flag{FAULT_FLAG_WRITE,FAULT_FLAG_MKWRITE,FAULT_FLAG_ALLOW_RETRY,FAULT_FLAG_RETRY_NOWAIT,FAULT_FLAG_KILLABLE,FAULT_FLAG_TRIED,FAULT_FLAG_USER,FAULT_FLAG_REMOTE,FAULT_FLAG_INSTRUCTION,FAULT_FLAG_INTERRUPTIBLE,FAULT_FLAG_UNSHARE,FAULT_FLAG_ORIG_PTE_VALID,FAULT_FLAG_VMA_LOCK};
typedef struct  page *pgtable_t;
struct  static_key{
atomic_t enabled;
union  {
unsigned long type;
struct  jump_entry *entries;
struct  static_key_mod *next;} ;};
struct  sigpending{
struct  list_head list;
sigset_t signal;};
struct  thread_group_cputimer{
struct  task_cputime_atomic cputime_atomic;};
struct  posix_cputimers{
struct  posix_cputimer_base bases[3];
unsigned int timers_active;
unsigned int expiry_active;};
typedef struct  {
seqcount_spinlock_t seqcount;
spinlock_t lock;} seqlock_t;
struct  task_io_accounting{
u64 rchar;
u64 wchar;
u64 syscr;
u64 syscw;
u64 read_bytes;
u64 write_bytes;
u64 cancelled_write_bytes;};
struct  pacct_struct{
int ac_flag;
long ac_exitcode;
unsigned long ac_mem;
u64 ac_utime;
u64 ac_stime;
unsigned long ac_minflt;
unsigned long ac_majflt;};
typedef unsigned int fmode_t;
struct  fown_struct{
rwlock_t lock;
struct  pid *pid;
enum pid_type pid_type;
kuid_t uid;
kuid_t euid;
int signum;};
struct  file_ra_state{
unsigned long start;
unsigned int size;
unsigned int async_size;
unsigned int ra_pages;
unsigned int mmap_miss;
loff_t prev_pos;};
struct  path{
struct  vfsmount *mnt;
struct  dentry *dentry;};
struct  ratelimit_state{
raw_spinlock_t lock;
int interval;
int burst;
int printed;
int missed;
unsigned long begin;
unsigned long flags;};
enum kobj_ns_type{KOBJ_NS_TYPE_NONE,KOBJ_NS_TYPE_NET,KOBJ_NS_TYPES};
struct  rcu_segcblist{
struct  callback_head *head;
struct  callback_head **tails[4];
unsigned long gp_seq[1];
long len;
long seglen[10];
u8 flags;};
struct  dl_bw{
raw_spinlock_t lock;
u64 bw;
u64 total_bw;};
struct  cpudl{
raw_spinlock_t lock;
int size;
cpumask_var_t free_cpus;
struct  cpudl_item *elements;};
struct  irq_work{
struct  __call_single_node node;
void (*func)(struct  irq_work*) ;
struct  rcuwait irqwait;};
struct  cpupri{
struct  cpupri_vec pri_to_cpu[101];
int *cpu_to_pri;};
struct  perf_event_pmu_context{
struct  pmu *pmu;
struct  perf_event_context *ctx;
struct  list_head pmu_ctx_entry;
struct  list_head pinned_active;
struct  list_head flexible_active;
unsigned int embedded:1;
unsigned int nr_events;
atomic_t refcount;
struct  callback_head callback_head;
void *task_ctx_data;
int rotate_necessary;};
struct  perf_event_groups{
struct  rb_root tree;
u64 index;};
typedef u64 phys_addr_t;
typedef unsigned long kernel_ulong_t;
struct  uid_gid_map{
u32 nr_extents;
union  {
struct  uid_gid_extent extent[5];
struct  {
struct  uid_gid_extent *forward;
struct  uid_gid_extent *reverse;} ;} ;};
struct  ns_common{
atomic_long_t stashed;
struct  proc_ns_operations *ops;
unsigned int inum;
refcount_t count;};
struct  ctl_table_set{
int (*is_seen)(struct  ctl_table_set*) ;
struct  ctl_dir dir;};
enum ucount_type{UCOUNT_USER_NAMESPACES,UCOUNT_PID_NAMESPACES,UCOUNT_UTS_NAMESPACES,UCOUNT_IPC_NAMESPACES,UCOUNT_NET_NAMESPACES,UCOUNT_MNT_NAMESPACES,UCOUNT_CGROUP_NAMESPACES,UCOUNT_TIME_NAMESPACES,UCOUNT_INOTIFY_INSTANCES,UCOUNT_INOTIFY_WATCHES,UCOUNT_COUNTS};
enum rlimit_type{UCOUNT_RLIMIT_NPROC,UCOUNT_RLIMIT_MSGQUEUE,UCOUNT_RLIMIT_SIGPENDING,UCOUNT_RLIMIT_MEMLOCK,UCOUNT_RLIMIT_COUNTS};
struct  trace_seq{
char buffer[6];
struct  seq_buf seq;
int full;};
typedef long long __kernel_time64_t;
enum dev_pm_qos_req_type{DEV_PM_QOS_RESUME_LATENCY,DEV_PM_QOS_LATENCY_TOLERANCE,DEV_PM_QOS_MIN_FREQUENCY,DEV_PM_QOS_MAX_FREQUENCY,DEV_PM_QOS_FLAGS};
struct  mem_dqblk{
qsize_t dqb_bhardlimit;
qsize_t dqb_bsoftlimit;
qsize_t dqb_curspace;
qsize_t dqb_rsvspace;
qsize_t dqb_ihardlimit;
qsize_t dqb_isoftlimit;
qsize_t dqb_curinodes;
time64_t dqb_btime;
time64_t dqb_itime;};
typedef void (*poll_queue_proc)(struct  file*,wait_queue_head_t*,struct  poll_table_struct*) ;
struct  qstr{
union  {
struct  {
u32 hash;
u32 len;} ;
u64 hash_len;} ;
unsigned char *name;};
struct  lockref{
union  {
__u64 lock_count;
struct  {
spinlock_t lock;
int count;} ;} ;};
struct  dev_links_info{
struct  list_head suppliers;
struct  list_head consumers;
struct  list_head defer_sync;
enum dl_dev_state status;};
struct  dev_pm_info{
pm_message_t power_state;
unsigned int can_wakeup:1;
unsigned int async_suspend:1;
bool in_dpm_list:1;
bool is_prepared:1;
bool is_suspended:1;
bool is_noirq_suspended:1;
bool is_late_suspended:1;
bool no_pm:1;
bool early_init:1;
bool direct_complete:1;
u32 driver_flags;
spinlock_t lock;
struct  list_head entry;
struct  completion completion;
struct  wakeup_source *wakeup;
bool wakeup_path:1;
bool syscore:1;
bool no_pm_callbacks:1;
unsigned int must_resume:1;
unsigned int may_skip_resume:1;
struct  hrtimer suspend_timer;
u64 timer_expires;
struct  work_struct work;
wait_queue_head_t wait_queue;
struct  wake_irq *wakeirq;
atomic_t usage_count;
atomic_t child_count;
unsigned int disable_depth:3;
unsigned int idle_notification:1;
unsigned int request_pending:1;
unsigned int deferred_resume:1;
unsigned int needs_force_resume:1;
unsigned int runtime_auto:1;
bool ignore_children:1;
unsigned int no_callbacks:1;
unsigned int irq_safe:1;
unsigned int use_autosuspend:1;
unsigned int timer_autosuspends:1;
unsigned int memalloc_noio:1;
unsigned int links_count;
enum rpm_request request;
enum rpm_status runtime_status;
enum rpm_status last_status;
int runtime_error;
int autosuspend_delay;
u64 last_busy;
u64 active_time;
u64 suspended_time;
u64 accounting_timestamp;
struct  pm_subsys_data *subsys_data;
void (*set_latency_tolerance)(struct  device*,s32) ;
struct  dev_pm_qos *qos;};
struct  dev_msi_info{
struct  irq_domain *domain;
struct  msi_device_data *data;};
struct  dev_archdata{
};
enum device_removable{DEVICE_REMOVABLE_NOT_SUPPORTED,DEVICE_REMOVABLE_UNKNOWN,DEVICE_FIXED,DEVICE_REMOVABLE};
struct  idr{
struct  xarray idr_rt;
unsigned int idr_base;
unsigned int idr_next;};
typedef int (*notifier_fn_t)(struct  notifier_block*,unsigned long,void*) ;
typedef s32 old_time32_t;
typedef int32_t key_serial_t;
typedef uint32_t key_perm_t;
enum probe_type{PROBE_DEFAULT_STRATEGY,PROBE_PREFER_ASYNCHRONOUS,PROBE_FORCE_SYNCHRONOUS};
struct  timespec64{
time64_t tv_sec;
long tv_nsec;};
enum uprobe_task_state{UTASK_RUNNING,UTASK_SSTEP,UTASK_SSTEP_ACK,UTASK_SSTEP_TRAPPED};
struct  freq_constraints{
struct  pm_qos_constraints min_freq;
struct  blocking_notifier_head min_freq_notifiers;
struct  pm_qos_constraints max_freq;
struct  blocking_notifier_head max_freq_notifiers;};
struct  pm_qos_flags{
struct  list_head list;
s32 effective_flags;};
enum device_physical_location_panel{DEVICE_PANEL_TOP,DEVICE_PANEL_BOTTOM,DEVICE_PANEL_LEFT,DEVICE_PANEL_RIGHT,DEVICE_PANEL_FRONT,DEVICE_PANEL_BACK,DEVICE_PANEL_UNKNOWN};
enum device_physical_location_vertical_position{DEVICE_VERT_POS_UPPER,DEVICE_VERT_POS_CENTER,DEVICE_VERT_POS_LOWER};
enum device_physical_location_horizontal_position{DEVICE_HORI_POS_LEFT,DEVICE_HORI_POS_CENTER,DEVICE_HORI_POS_RIGHT};
typedef bool (*filldir_t)(struct  dir_context*,char*,int,loff_t,u64,unsigned int) ;
struct  u64_stats_sync{
};
struct  attribute{
char *name;
umode_t mode;};
struct  address_space{
struct  inode *host;
struct  xarray i_pages;
struct  rw_semaphore invalidate_lock;
gfp_t gfp_mask;
atomic_t i_mmap_writable;
struct  rb_root_cached i_mmap;
unsigned long nrpages;
unsigned long writeback_index;
struct  address_space_operations *a_ops;
unsigned long flags;
struct  rw_semaphore i_mmap_rwsem;
errseq_t wb_err;
spinlock_t private_lock;
struct  list_head private_list;
void *private_data;};
typedef struct  pgprot pgprot_t;
struct  vm_userfaultfd_ctx{
};
enum perf_event_state{PERF_EVENT_STATE_DEAD,PERF_EVENT_STATE_EXIT,PERF_EVENT_STATE_ERROR,PERF_EVENT_STATE_OFF,PERF_EVENT_STATE_INACTIVE,PERF_EVENT_STATE_ACTIVE};
struct  perf_event_attr{
__u32 type;
__u32 size;
__u64 config;
union  {
__u64 sample_period;
__u64 sample_freq;} ;
__u64 sample_type;
__u64 read_format;
__u64 disabled:1;
__u64 inherit:1;
__u64 pinned:1;
__u64 exclusive:1;
__u64 exclude_user:1;
__u64 exclude_kernel:1;
__u64 exclude_hv:1;
__u64 exclude_idle:1;
__u64 mmap:1;
__u64 comm:1;
__u64 freq:1;
__u64 inherit_stat:1;
__u64 enable_on_exec:1;
__u64 task:1;
__u64 watermark:1;
__u64 precise_ip:2;
__u64 mmap_data:1;
__u64 sample_id_all:1;
__u64 exclude_host:1;
__u64 exclude_guest:1;
__u64 exclude_callchain_kernel:1;
__u64 exclude_callchain_user:1;
__u64 mmap2:1;
__u64 comm_exec:1;
__u64 use_clockid:1;
__u64 context_switch:1;
__u64 write_backward:1;
__u64 namespaces:1;
__u64 ksymbol:1;
__u64 bpf_event:1;
__u64 aux_output:1;
__u64 cgroup:1;
__u64 text_poke:1;
__u64 build_id:1;
__u64 inherit_thread:1;
__u64 remove_on_exec:1;
__u64 sigtrap:1;
__u64 __reserved_1:26;
union  {
__u32 wakeup_events;
__u32 wakeup_watermark;} ;
__u32 bp_type;
union  {
__u64 bp_addr;
__u64 kprobe_func;
__u64 uprobe_path;
__u64 config1;} ;
union  {
__u64 bp_len;
__u64 kprobe_addr;
__u64 probe_offset;
__u64 config2;} ;
__u64 branch_sample_type;
__u64 sample_regs_user;
__u32 sample_stack_user;
__s32 clockid;
__u64 sample_regs_intr;
__u32 aux_watermark;
__u16 sample_max_stack;
__u16 __reserved_2;
__u32 aux_sample_size;
__u32 __reserved_3;
__u64 sig_data;
__u64 config3;};
struct  hw_perf_event{
union  {
struct  {
u64 config;
u64 last_tag;
unsigned long config_base;
unsigned long event_base;
int event_base_rdpmc;
int idx;
int last_cpu;
int flags;
struct  hw_perf_event_extra extra_reg;
struct  hw_perf_event_extra branch_reg;} ;
struct  {
struct  hrtimer hrtimer;} ;
struct  {
struct  list_head tp_list;} ;
struct  {
u64 pwr_acc;
u64 ptsc;} ;
struct  {
struct  arch_hw_breakpoint info;
struct  rhlist_head bp_list;} ;
struct  {
u8 iommu_bank;
u8 iommu_cntr;
u16 padding;
u64 conf;
u64 conf1;} ;} ;
struct  task_struct *target;
void *addr_filters;
unsigned long addr_filters_gen;
int state;
local64_t prev_count;
u64 sample_period;
union  {
struct  {
u64 last_period;
local64_t period_left;} ;
struct  {
u64 saved_metric;
u64 saved_slots;} ;} ;
u64 interrupts_seq;
u64 interrupts;
u64 freq_time_stamp;
u64 freq_count_stamp;};
struct  perf_addr_filters_head{
struct  list_head list;
raw_spinlock_t lock;
unsigned int nr_file_filters;};
typedef void (*perf_overflow_handler_t)(struct  perf_event*,struct  perf_sample_data*,struct  pt_regs*) ;
struct  list_lru_one{
struct  list_head list;
long nr_items;};
struct  sched_entity{
struct  load_weight load;
struct  rb_node run_node;
u64 deadline;
u64 min_deadline;
struct  list_head group_node;
unsigned int on_rq;
u64 exec_start;
u64 sum_exec_runtime;
u64 prev_sum_exec_runtime;
u64 vruntime;
s64 vlag;
u64 slice;
u64 nr_migrations;
int depth;
struct  sched_entity *parent;
struct  cfs_rq *cfs_rq;
struct  cfs_rq *my_q;
unsigned long runnable_weight;
struct  sched_avg avg;};
struct  thread_info{
unsigned long flags;
unsigned long syscall_work;
u32 status;
u32 cpu;};
struct  sched_rt_entity{
struct  list_head run_list;
unsigned long timeout;
unsigned long watchdog_stamp;
unsigned int time_slice;
unsigned short on_rq;
unsigned short on_list;
struct  sched_rt_entity *back;};
struct  sched_dl_entity{
struct  rb_node rb_node;
u64 dl_runtime;
u64 dl_deadline;
u64 dl_period;
u64 dl_bw;
u64 dl_density;
s64 runtime;
u64 deadline;
unsigned int flags;
unsigned int dl_throttled:1;
unsigned int dl_yielded:1;
unsigned int dl_non_contending:1;
unsigned int dl_overrun:1;
struct  hrtimer dl_timer;
struct  hrtimer inactive_timer;
struct  sched_dl_entity *pi_se;};
struct  sched_statistics{
u64 wait_start;
u64 wait_max;
u64 wait_count;
u64 wait_sum;
u64 iowait_count;
u64 iowait_sum;
u64 sleep_start;
u64 sleep_max;
s64 sum_sleep_runtime;
u64 block_start;
u64 block_max;
s64 sum_block_runtime;
u64 exec_max;
u64 slice_max;
u64 nr_migrations_cold;
u64 nr_failed_migrations_affine;
u64 nr_failed_migrations_running;
u64 nr_failed_migrations_hot;
u64 nr_forced_migrations;
u64 nr_wakeups;
u64 nr_wakeups_sync;
u64 nr_wakeups_migrate;
u64 nr_wakeups_local;
u64 nr_wakeups_remote;
u64 nr_wakeups_affine;
u64 nr_wakeups_affine_attempts;
u64 nr_wakeups_passive;
u64 nr_wakeups_idle;};
union  rcu_special{
struct  {
u8 blocked;
u8 need_qs;
u8 exp_hint;
u8 need_mb;} b;
u32 s;};
struct  sched_info{
unsigned long pcount;
unsigned long long run_delay;
unsigned long long last_arrival;
unsigned long long last_queued;};
struct  restart_block{
unsigned long arch_data;
long (*fn)(struct  restart_block*) ;
union  {
struct  {
u32 *uaddr;
u32 val;
u32 flags;
u32 bitset;
u64 time;
u32 *uaddr2;} futex;
struct  {
clockid_t clockid;
enum timespec_type type;
union  {
struct  __kernel_timespec *rmtp;
struct  old_timespec32 *compat_rmtp;} ;
u64 expires;} nanosleep;
struct  {
struct  pollfd *ufds;
int nfds;
int has_timeout;
unsigned long tv_sec;
unsigned long tv_nsec;} poll;} ;};
typedef __kernel_pid_t pid_t;
struct  posix_cputimers_work{
struct  callback_head work;
struct  mutex mutex;
unsigned int scheduled;};
struct  sysv_sem{
struct  sem_undo_list *undo_list;};
struct  sysv_shm{
struct  list_head shm_clist;};
struct  seccomp{
int mode;
atomic_t filter_count;
struct  seccomp_filter *filter;};
struct  syscall_user_dispatch{
char *selector;
unsigned long offset;
unsigned long len;
bool on_dispatch;};
struct  wake_q_node{
struct  wake_q_node *next;};
struct  tlbflush_unmap_batch{
struct  arch_tlbflush_unmap_batch arch;
bool flush_required;
bool writable;};
struct  page_frag{
struct  page *page;
__u32 offset;
__u32 size;};
struct  kmap_ctrl{
};
struct  llist_head{
struct  llist_node *first;};
struct  thread_struct{
struct  desc_struct tls_array[3];
unsigned long sp;
unsigned short es;
unsigned short ds;
unsigned short fsindex;
unsigned short gsindex;
unsigned long fsbase;
unsigned long gsbase;
struct  perf_event *ptrace_bps[4];
unsigned long virtual_dr6;
unsigned long ptrace_dr7;
unsigned long cr2;
unsigned long trap_nr;
unsigned long error_code;
struct  io_bitmap *io_bitmap;
unsigned long iopl_emul;
unsigned int iopl_warn:1;
unsigned int sig_on_uaccess_err:1;
u32 pkru;
struct  fpu fpu;};
enum module_state{MODULE_STATE_LIVE,MODULE_STATE_COMING,MODULE_STATE_GOING,MODULE_STATE_UNFORMED};
struct  module_kobject{
struct  kobject kobj;
struct  module *mod;
struct  kobject *drivers_dir;
struct  module_param_attrs *mp;
struct  completion *kobj_completion;};
enum mod_mem_type{MOD_TEXT,MOD_DATA,MOD_RODATA,MOD_RO_AFTER_INIT,MOD_INIT_TEXT,MOD_INIT_DATA,MOD_INIT_RODATA,MOD_MEM_NUM_TYPES,MOD_INVALID};
struct  mod_arch_specific{
unsigned int num_orcs;
int *orc_unwind_ip;
struct  orc_entry *orc_unwind;};
struct  mod_kallsyms{
Elf64_Sym *symtab;
unsigned int num_symtab;
char *strtab;
char *typetab;};
typedef struct  wait_queue_entry wait_queue_entry_t;
typedef __s8 s8;
struct  cfs_rq{
struct  load_weight load;
unsigned int nr_running;
unsigned int h_nr_running;
unsigned int idle_nr_running;
unsigned int idle_h_nr_running;
s64 avg_vruntime;
u64 avg_load;
u64 exec_clock;
u64 min_vruntime;
struct  rb_root_cached tasks_timeline;
struct  sched_entity *curr;
struct  sched_entity *next;
struct  sched_avg avg;
struct  {
raw_spinlock_t lock;
int nr;
unsigned long load_avg;
unsigned long util_avg;
unsigned long runnable_avg;} removed;
unsigned long tg_load_avg_contrib;
long propagate;
long prop_runnable_sum;
unsigned long h_load;
u64 last_h_load_update;
struct  sched_entity *h_load_next;
struct  rq *rq;
int on_list;
struct  list_head leaf_cfs_rq_list;
struct  task_group *tg;
int idle;};
typedef struct  __call_single_data call_single_data_t;
struct  rt_rq{
struct  rt_prio_array active;
unsigned int rt_nr_running;
unsigned int rr_nr_running;
struct  {
int curr;
int next;} highest_prio;
unsigned int rt_nr_migratory;
unsigned int rt_nr_total;
int overloaded;
struct  plist_head pushable_tasks;
int rt_queued;
int rt_throttled;
u64 rt_time;
u64 rt_runtime;
raw_spinlock_t rt_runtime_lock;};
struct  dl_rq{
struct  rb_root_cached root;
unsigned int dl_nr_running;
struct  {
u64 curr;
u64 next;} earliest_dl;
unsigned int dl_nr_migratory;
int overloaded;
struct  rb_root_cached pushable_dl_tasks_root;
u64 running_bw;
u64 this_bw;
u64 extra_bw;
u64 max_bw;
u64 bw_ratio;};
struct  cpu_stop_work{
struct  list_head list;
cpu_stop_fn_t fn;
unsigned long caller;
void *arg;
struct  cpu_stop_done *done;};
union  perf_sample_weight{
__u64 full;
struct  {
__u32 var1_dw;
__u16 var2_w;
__u16 var3_w;} ;};
union  perf_mem_data_src{
__u64 val;
struct  {
__u64 mem_op:5;
__u64 mem_lvl:14;
__u64 mem_snoop:5;
__u64 mem_lock:2;
__u64 mem_dtlb:7;
__u64 mem_lvl_num:4;
__u64 mem_remote:1;
__u64 mem_snoopx:2;
__u64 mem_blk:3;
__u64 mem_hops:3;
__u64 mem_rsvd:18;} ;};
struct  perf_regs{
__u64 abi;
struct  pt_regs *regs;};
struct  hlist_bl_head{
struct  hlist_bl_node *first;};
struct  quota_info{
unsigned int flags;
struct  rw_semaphore dqio_sem;
struct  inode *files[3];
struct  mem_dqinfo info[3];
struct  quota_format_ops *ops[3];};
struct  sb_writers{
unsigned short frozen;
unsigned short freeze_holders;
struct  percpu_rw_semaphore rw_sem[3];};
typedef struct  {
__u8 b[16];} uuid_t;
struct  shrinker{
unsigned long (*count_objects)(struct  shrinker*,struct  shrink_control*) ;
unsigned long (*scan_objects)(struct  shrinker*,struct  shrink_control*) ;
long batch;
int seeks;
unsigned int flags;
struct  list_head list;
atomic_long_t *nr_deferred;};
struct  list_lru{
struct  list_lru_node *node;};
struct  pin_cookie{
};
enum hrtimer_base_type{HRTIMER_BASE_MONOTONIC,HRTIMER_BASE_REALTIME,HRTIMER_BASE_BOOTTIME,HRTIMER_BASE_TAI,HRTIMER_BASE_MONOTONIC_SOFT,HRTIMER_BASE_REALTIME_SOFT,HRTIMER_BASE_BOOTTIME_SOFT,HRTIMER_BASE_TAI_SOFT,HRTIMER_MAX_CLOCK_BASES};
struct  core_thread{
struct  task_struct *task;
struct  core_thread *next;};
typedef int (*proc_handler )(struct  ctl_table*,int,void*,size_t*,loff_t*) ;
struct  cgroup{
struct  cgroup_subsys_state self;
unsigned long flags;
int level;
int max_depth;
int nr_descendants;
int nr_dying_descendants;
int max_descendants;
int nr_populated_csets;
int nr_populated_domain_children;
int nr_populated_threaded_children;
int nr_threaded_children;
struct  kernfs_node *kn;
struct  cgroup_file procs_file;
struct  cgroup_file events_file;
struct  cgroup_file psi_files[0];
u16 subtree_control;
u16 subtree_ss_mask;
u16 old_subtree_control;
u16 old_subtree_ss_mask;
struct  cgroup_subsys_state *subsys[14];
struct  cgroup_root *root;
struct  list_head cset_links;
struct  list_head e_csets[100];
struct  cgroup *dom_cgrp;
struct  cgroup *old_dom_cgrp;
struct  cgroup_rstat_cpu *rstat_cpu;
struct  list_head rstat_css_list;
struct  cgroup_base_stat last_bstat;
struct  cgroup_base_stat bstat;
struct  prev_cputime prev_cputime;
struct  list_head pidlists;
struct  mutex pidlist_mutex;
wait_queue_head_t offline_waitq;
struct  work_struct release_agent_work;
struct  psi_group *psi;
struct  cgroup_bpf bpf;
atomic_t congestion_count;
struct  cgroup_freezer_state freezer;
struct  cgroup *ancestors[];};
struct  vmem_altmap{
unsigned long base_pfn;
unsigned long end_pfn;
unsigned long reserve;
unsigned long free;
unsigned long align;
unsigned long alloc;};
enum memory_type{MEMORY_DEVICE_PRIVATE,MEMORY_DEVICE_COHERENT,MEMORY_DEVICE_FS_DAX,MEMORY_DEVICE_GENERIC,MEMORY_DEVICE_PCI_P2PDMA};
typedef void (*percpu_ref_func_t )(struct  percpu_ref*) ;
struct  dev_pm_ops{
int (*prepare)(struct  device*) ;
void (*complete)(struct  device*) ;
int (*suspend)(struct  device*) ;
int (*resume)(struct  device*) ;
int (*freeze)(struct  device*) ;
int (*thaw)(struct  device*) ;
int (*poweroff)(struct  device*) ;
int (*restore)(struct  device*) ;
int (*suspend_late)(struct  device*) ;
int (*resume_early)(struct  device*) ;
int (*freeze_late)(struct  device*) ;
int (*thaw_early)(struct  device*) ;
int (*poweroff_late)(struct  device*) ;
int (*restore_early)(struct  device*) ;
int (*suspend_noirq)(struct  device*) ;
int (*resume_noirq)(struct  device*) ;
int (*freeze_noirq)(struct  device*) ;
int (*thaw_noirq)(struct  device*) ;
int (*poweroff_noirq)(struct  device*) ;
int (*restore_noirq)(struct  device*) ;
int (*runtime_suspend)(struct  device*) ;
int (*runtime_resume)(struct  device*) ;
int (*runtime_idle)(struct  device*) ;};
struct  cfs_bandwidth{
};
struct  delayed_work{
struct  work_struct work;
struct  timer_list timer;
struct  workqueue_struct *wq;
int cpu;};
typedef struct  {
u64 val;} kernel_cap_t;
struct  lockdep_map{
};
typedef u32 phandle;
struct  fwnode_handle{
struct  fwnode_handle *secondary;
struct  fwnode_operations *ops;
struct  device *dev;
struct  list_head suppliers;
struct  list_head consumers;
u8 flags;};
struct  seq_file{
char *buf;
size_t size;
size_t from;
size_t count;
size_t pad_until;
loff_t index;
loff_t read_pos;
struct  mutex lock;
struct  seq_operations *op;
int poll_event;
struct  file *file;
void *private;};
struct  kobj_type{
void (*release)(struct  kobject*) ;
struct  sysfs_ops *sysfs_ops;
struct  attribute_group **default_groups;
struct  kobj_ns_type_operations* (*child_ns_type)(struct  kobject*) ;
void* (*namespace)(struct  kobject*) ;
void (*get_ownership)(struct  kobject*,kuid_t*,kgid_t*) ;};
struct  key_restriction{
key_restrict_link_func_t check;
struct  key *key;
struct  key_type *keytype;};
struct  perf_raw_record{
struct  perf_raw_frag frag;
u32 size;};
enum cpu_util_type{FREQUENCY_UTIL,ENERGY_UTIL};
struct  trace_event_functions{
trace_print_func trace;
trace_print_func raw;
trace_print_func hex;
trace_print_func binary;};
struct  sched_domain{
struct  sched_domain *parent;
struct  sched_domain *child;
struct  sched_group *groups;
unsigned long min_interval;
unsigned long max_interval;
unsigned int busy_factor;
unsigned int imbalance_pct;
unsigned int cache_nice_tries;
unsigned int imb_numa_nr;
int nohz_idle;
int flags;
int level;
unsigned long last_balance;
unsigned int balance_interval;
unsigned int nr_balance_failed;
u64 max_newidle_lb_cost;
unsigned long last_decay_max_lb_cost;
u64 avg_scan_cost;
unsigned int lb_count[3];
unsigned int lb_failed[3];
unsigned int lb_balanced[3];
unsigned int lb_imbalance[3];
unsigned int lb_gained[3];
unsigned int lb_hot_gained[3];
unsigned int lb_nobusyg[3];
unsigned int lb_nobusyq[3];
unsigned int alb_count;
unsigned int alb_failed;
unsigned int alb_pushed;
unsigned int sbe_count;
unsigned int sbe_balanced;
unsigned int sbe_pushed;
unsigned int sbf_count;
unsigned int sbf_balanced;
unsigned int sbf_pushed;
unsigned int ttwu_wake_remote;
unsigned int ttwu_move_affine;
unsigned int ttwu_move_balance;
union  {
void *private;
struct  callback_head rcu;} ;
struct  sched_domain_shared *shared;
unsigned int span_weight;
unsigned long span[1];};
struct  trace_event_call{
struct  list_head list;
struct  trace_event_class *class;
union  {
char *name;
struct  tracepoint *tp;} ;
struct  trace_event event;
char *print_fmt;
struct  event_filter *filter;
union  {
void *module;
atomic_t refcnt;} ;
void *data;
int flags;
int perf_refcount;
struct  hlist_head *perf_events;
struct  bpf_prog_array *prog_array;
int (*perf_perm)(struct  trace_event_call*,struct  perf_event*) ;};
struct  cpudl_item{
u64 dl;
int cpu;
int idx;};
struct  kset_uevent_ops{
int (*filter)(struct  kobject*) ;
char* (*name)(struct  kobject*) ;
int (*uevent)(struct  kobject*,struct  kobj_uevent_env*) ;};
struct  trace_event_fields{
char *type;
union  {
struct  {
char *name;
int size;
int align;
int is_signed;
int filter_type;
int len;} ;
int (*define_fields)(struct  trace_event_call*) ;} ;};
struct  kiocb{
struct  file *ki_filp;
loff_t ki_pos;
void (*ki_complete)(struct  kiocb*,long) ;
void *private;
int ki_flags;
u16 ki_ioprio;
union  {
struct  wait_page_queue *ki_waitq;
ssize_t (*dio_complete)(void*) ;} ;};
struct  pm_subsys_data{
spinlock_t lock;
unsigned int refcount;};
struct  kobj_uevent_env{
char *argv[3];
char *envp[3];
int envp_idx;
char buf[6];
int buflen;};
struct  sched_domain_shared{
atomic_t ref;
atomic_t nr_busy_cpus;
int has_idle_cores;
int nr_idle_scan;};
struct  address_space_operations{
int (*writepage)(struct  page*,struct  writeback_control*) ;
int (*read_folio)(struct  file*,struct  folio*) ;
int (*writepages)(struct  address_space*,struct  writeback_control*) ;
bool (*dirty_folio)(struct  address_space*,struct  folio*) ;
void (*readahead)(struct  readahead_control*) ;
int (*write_begin)(struct  file*,struct  address_space*,loff_t,unsigned int,struct  page**,void**) ;
int (*write_end)(struct  file*,struct  address_space*,loff_t,unsigned int,unsigned int,struct  page*,void*) ;
sector_t (*bmap)(struct  address_space*,sector_t) ;
void (*invalidate_folio)(struct  folio*,size_t,size_t) ;
bool (*release_folio)(struct  folio*,gfp_t) ;
void (*free_folio)(struct  folio*) ;
ssize_t (*direct_IO)(struct  kiocb*,struct  iov_iter*) ;
int (*migrate_folio)(struct  address_space*,struct  folio*,struct  folio*,enum migrate_mode) ;
int (*launder_folio)(struct  folio*) ;
bool (*is_partially_uptodate)(struct  folio*,size_t,size_t) ;
void (*is_dirty_writeback)(struct  folio*,bool*,bool*) ;
int (*error_remove_page)(struct  address_space*,struct  page*) ;
int (*swap_activate)(struct  swap_info_struct*,struct  file*,sector_t*) ;
void (*swap_deactivate)(struct  file*) ;
int (*swap_rw)(struct  kiocb*,struct  iov_iter*) ;};
struct  taskstats{
__u16 version;
__u32 ac_exitcode;
__u8 ac_flag;
__u8 ac_nice;
__u64 cpu_count;
__u64 cpu_delay_total;
__u64 blkio_count;
__u64 blkio_delay_total;
__u64 swapin_count;
__u64 swapin_delay_total;
__u64 cpu_run_real_total;
__u64 cpu_run_virtual_total;
char ac_comm[6];
__u8 ac_sched;
__u8 ac_pad[16];
__u32 ac_uid;
__u32 ac_gid;
__u32 ac_pid;
__u32 ac_ppid;
__u32 ac_btime;
__u64 ac_etime;
__u64 ac_utime;
__u64 ac_stime;
__u64 ac_minflt;
__u64 ac_majflt;
__u64 coremem;
__u64 virtmem;
__u64 hiwater_rss;
__u64 hiwater_vm;
__u64 read_char;
__u64 write_char;
__u64 read_syscalls;
__u64 write_syscalls;
__u64 read_bytes;
__u64 write_bytes;
__u64 cancelled_write_bytes;
__u64 nvcsw;
__u64 nivcsw;
__u64 ac_utimescaled;
__u64 ac_stimescaled;
__u64 cpu_scaled_run_real_total;
__u64 freepages_count;
__u64 freepages_delay_total;
__u64 thrashing_count;
__u64 thrashing_delay_total;
__u64 ac_btime64;
__u64 compact_count;
__u64 compact_delay_total;
__u32 ac_tgid;
__u64 ac_tgetime;
__u64 ac_exe_dev;
__u64 ac_exe_inode;
__u64 wpcopy_count;
__u64 wpcopy_delay_total;
__u64 irq_count;
__u64 irq_delay_total;};
struct  exception_table_entry{
int insn;
int fixup;
int data;};
struct  vm_fault{
struct  {
struct  vm_area_struct *vma;
gfp_t gfp_mask;
unsigned long pgoff;
unsigned long address;
unsigned long real_address;} ;
enum fault_flag flags;
pmd_t *pmd;
pud_t *pud;
union  {
pte_t orig_pte;
pmd_t orig_pmd;} ;
struct  page *cow_page;
struct  page *page;
pte_t *pte;
spinlock_t *ptl;
pgtable_t prealloc_pte;};
struct  tracepoint{
char *name;
struct  static_key key;
struct  static_call_key *static_call_key;
void *static_call_tramp;
void *iterator;
void *probestub;
int (*regfunc)() ;
void (*unregfunc)() ;
struct  tracepoint_func *funcs;};
struct  signal_struct{
refcount_t sigcnt;
atomic_t live;
int nr_threads;
int quick_threads;
struct  list_head thread_head;
wait_queue_head_t wait_chldexit;
struct  task_struct *curr_target;
struct  sigpending shared_pending;
struct  hlist_head multiprocess;
int group_exit_code;
int notify_count;
struct  task_struct *group_exec_task;
int group_stop_count;
unsigned int flags;
struct  core_state *core_state;
unsigned int is_child_subreaper:1;
unsigned int has_child_subreaper:1;
unsigned int next_posix_timer_id;
struct  list_head posix_timers;
struct  hrtimer real_timer;
ktime_t it_real_incr;
struct  cpu_itimer it[2];
struct  thread_group_cputimer cputimer;
struct  posix_cputimers posix_cputimers;
struct  pid *pids[4];
struct  pid *tty_old_pgrp;
int leader;
struct  tty_struct *tty;
seqlock_t stats_lock;
u64 utime;
u64 stime;
u64 cutime;
u64 cstime;
u64 gtime;
u64 cgtime;
struct  prev_cputime prev_cputime;
unsigned long nvcsw;
unsigned long nivcsw;
unsigned long cnvcsw;
unsigned long cnivcsw;
unsigned long min_flt;
unsigned long maj_flt;
unsigned long cmin_flt;
unsigned long cmaj_flt;
unsigned long inblock;
unsigned long oublock;
unsigned long cinblock;
unsigned long coublock;
unsigned long maxrss;
unsigned long cmaxrss;
struct  task_io_accounting ioac;
unsigned long long sum_sched_runtime;
struct  rlimit rlim[16];
struct  pacct_struct pacct;
struct  taskstats *stats;
unsigned int audit_tty;
struct  tty_audit_buf *tty_audit_buf;
bool oom_flag_origin;
short oom_score_adj;
short oom_score_adj_min;
struct  mm_struct *oom_mm;
struct  mutex cred_guard_mutex;
struct  rw_semaphore exec_update_lock;};
struct  pollfd{
int fd;
short events;
short revents;};
struct  linux_binprm{
struct  vm_area_struct *vma;
unsigned long vma_pages;
struct  mm_struct *mm;
unsigned long p;
unsigned long argmin;
unsigned int have_execfd:1;
unsigned int execfd_creds:1;
unsigned int secureexec:1;
unsigned int point_of_no_return:1;
struct  file *executable;
struct  file *interpreter;
struct  file *file;
struct  cred *cred;
int unsafe;
unsigned int per_clear;
int argc;
int envc;
char *filename;
char *interp;
char *fdpath;
unsigned int interp_flags;
int execfd;
unsigned long loader;
unsigned long exec;
struct  rlimit rlim_stack;
char buf[6];};
struct  em_perf_domain{
struct  em_perf_state *table;
int nr_perf_states;
unsigned long flags;
unsigned long cpus[1];};
struct  bus_type{
char *name;
char *dev_name;
struct  attribute_group **bus_groups;
struct  attribute_group **dev_groups;
struct  attribute_group **drv_groups;
int (*match)(struct  device*,struct  device_driver*) ;
int (*uevent)(struct  device*,struct  kobj_uevent_env*) ;
int (*probe)(struct  device*) ;
void (*sync_state)(struct  device*) ;
void (*remove)(struct  device*) ;
void (*shutdown)(struct  device*) ;
int (*online)(struct  device*) ;
int (*offline)(struct  device*) ;
int (*suspend)(struct  device*,pm_message_t) ;
int (*resume)(struct  device*) ;
int (*num_vf)(struct  device*) ;
int (*dma_configure)(struct  device*) ;
void (*dma_cleanup)(struct  device*) ;
struct  dev_pm_ops *pm;
struct  iommu_ops *iommu_ops;
bool need_parent_lock;};
struct  file{
union  {
struct  llist_node f_llist;
struct  callback_head f_rcuhead;
unsigned int f_iocb_flags;} ;
spinlock_t f_lock;
fmode_t f_mode;
atomic_long_t f_count;
struct  mutex f_pos_lock;
loff_t f_pos;
unsigned int f_flags;
struct  fown_struct f_owner;
struct  cred *f_cred;
struct  file_ra_state f_ra;
struct  path f_path;
struct  inode *f_inode;
struct  file_operations *f_op;
u64 f_version;
void *f_security;
void *private_data;
struct  hlist_head *f_ep;
struct  address_space *f_mapping;
errseq_t f_wb_err;
errseq_t f_sb_err;};
struct  of_device_id{
char name[6];
char type[6];
char compatible[6];
void *data;};
struct  user_struct{
refcount_t __count;
struct  percpu_counter epoll_watches;
unsigned long unix_inflight;
atomic_long_t pipe_bufs;
struct  hlist_node uidhash_node;
kuid_t uid;
atomic_long_t locked_vm;
struct  ratelimit_state ratelimit;};
struct  kobj_ns_type_operations{
enum kobj_ns_type type;
bool (*current_may_mount)() ;
void* (*grab_current_ns)() ;
void* (*netlink_ns)(struct  sock*) ;
void* (*initial_ns)() ;
void (*drop_ns)(void*) ;};
struct  math_emu_info{
long ___orig_eip;
struct  pt_regs *regs;};
struct  static_call_mod{
struct  static_call_mod *next;
struct  module *mod;
struct  static_call_site *sites;};
struct  sighand_struct{
spinlock_t siglock;
refcount_t count;
wait_queue_head_t signalfd_wqh;
struct  k_sigaction action[64];};
struct  quotactl_ops{
int (*quota_on)(struct  super_block*,int,int,struct  path*) ;
int (*quota_off)(struct  super_block*,int) ;
int (*quota_enable)(struct  super_block*,unsigned int) ;
int (*quota_disable)(struct  super_block*,unsigned int) ;
int (*quota_sync)(struct  super_block*,int) ;
int (*set_info)(struct  super_block*,int,struct  qc_info*) ;
int (*get_dqblk)(struct  super_block*,struct  kqid,struct  qc_dqblk*) ;
int (*get_nextdqblk)(struct  super_block*,struct  kqid*,struct  qc_dqblk*) ;
int (*set_dqblk)(struct  super_block*,struct  kqid,struct  qc_dqblk*) ;
int (*get_state)(struct  super_block*,struct  qc_state*) ;
int (*rm_xquota)(struct  super_block*,unsigned int) ;};
struct  srcu_data{
atomic_long_t srcu_lock_count[10];
atomic_long_t srcu_unlock_count[10];
int srcu_nmi_safety;
spinlock_t lock;
struct  rcu_segcblist srcu_cblist;
unsigned long srcu_gp_seq_needed;
unsigned long srcu_gp_seq_needed_exp;
bool srcu_cblist_invoking;
struct  timer_list delay_work;
struct  work_struct work;
struct  callback_head srcu_barrier_head;
struct  srcu_node *mynode;
unsigned long grpmask;
int cpu;
struct  srcu_struct *ssp;};
struct  root_domain{
atomic_t refcount;
atomic_t rto_count;
struct  callback_head rcu;
cpumask_var_t span;
cpumask_var_t online;
int overload;
int overutilized;
cpumask_var_t dlo_mask;
atomic_t dlo_count;
struct  dl_bw dl_bw;
struct  cpudl cpudl;
u64 visit_gen;
struct  irq_work rto_push_work;
raw_spinlock_t rto_lock;
int rto_loop;
int rto_cpu;
atomic_t rto_loop_next;
atomic_t rto_loop_start;
cpumask_var_t rto_mask;
struct  cpupri cpupri;
unsigned long max_cpu_capacity;
struct  perf_domain *pd;};
struct  perf_cgroup{
struct  cgroup_subsys_state css;
struct  perf_cgroup_info *info;};
struct  perf_cpu_pmu_context{
struct  perf_event_pmu_context epc;
struct  perf_event_pmu_context *task_epc;
struct  list_head sched_cb_entry;
int sched_cb_usage;
int active_oncpu;
int exclusive;
raw_spinlock_t hrtimer_lock;
struct  hrtimer hrtimer;
ktime_t hrtimer_interval;
unsigned int hrtimer_active;};
struct  perf_event_context{
raw_spinlock_t lock;
struct  mutex mutex;
struct  list_head pmu_ctx_list;
struct  perf_event_groups pinned_groups;
struct  perf_event_groups flexible_groups;
struct  list_head event_list;
int nr_events;
int nr_user;
int is_active;
int nr_task_data;
int nr_stat;
int nr_freq;
int rotate_disable;
refcount_t refcount;
struct  task_struct *task;
u64 time;
u64 timestamp;
u64 timeoffset;
struct  perf_event_context *parent_ctx;
u64 parent_gen;
u64 generation;
int pin_count;
int nr_cgroups;
struct  callback_head callback_head;
local_t nr_pending;};
struct  vm_struct{
struct  vm_struct *next;
void *addr;
unsigned long size;
unsigned long flags;
struct  page **pages;
unsigned int page_order;
unsigned int nr_pages;
phys_addr_t phys_addr;
void *caller;};
struct  trace_entry{
unsigned short type;
unsigned char flags;
unsigned char preempt_count;
int pid;};
struct  device_type{
char *name;
struct  attribute_group **groups;
int (*uevent)(struct  device*,struct  kobj_uevent_env*) ;
char* (*devnode)(struct  device*,umode_t*,kuid_t*,kgid_t*) ;
void (*release)(struct  device*) ;
struct  dev_pm_ops *pm;};
struct  acpi_device_id{
__u8 id[16];
kernel_ulong_t driver_data;
__u32 cls;
__u32 cls_msk;};
struct  fwnode_reference_args{
struct  fwnode_handle *fwnode;
unsigned int nargs;
u64 args[8];};
struct  user_namespace{
struct  uid_gid_map uid_map;
struct  uid_gid_map gid_map;
struct  uid_gid_map projid_map;
struct  user_namespace *parent;
int level;
kuid_t owner;
kgid_t group;
struct  ns_common ns;
unsigned long flags;
bool parent_could_setfcap;
struct  list_head keyring_name_list;
struct  key *user_keyring_register;
struct  rw_semaphore keyring_sem;
struct  work_struct work;
struct  ctl_table_set set;
struct  ctl_table_header *sysctls;
struct  ucounts *ucounts;
long ucount_max[10];
long rlimit_max[10];};
struct  tracepoint_func{
void *func;
void *data;
int prio;};
struct  trace_iterator{
struct  trace_array *tr;
struct  tracer *trace;
struct  array_buffer *array_buffer;
void *private;
int cpu_file;
struct  mutex mutex;
struct  ring_buffer_iter **buffer_iter;
unsigned long iter_flags;
void *temp;
unsigned int temp_size;
char *fmt;
unsigned int fmt_size;
long wait_index;
struct  trace_seq tmp_seq;
cpumask_var_t started;
bool snapshot;
struct  trace_seq seq;
struct  trace_entry *ent;
unsigned long lost_events;
int leftover;
int ent_size;
int cpu;
u64 ts;
loff_t pos;
long idx;};
struct  super_operations{
struct  inode* (*alloc_inode)(struct  super_block*) ;
void (*destroy_inode)(struct  inode*) ;
void (*free_inode)(struct  inode*) ;
void (*dirty_inode)(struct  inode*,int) ;
int (*write_inode)(struct  inode*,struct  writeback_control*) ;
int (*drop_inode)(struct  inode*) ;
void (*evict_inode)(struct  inode*) ;
void (*put_super)(struct  super_block*) ;
int (*sync_fs)(struct  super_block*,int) ;
int (*freeze_super)(struct  super_block*,enum freeze_holder) ;
int (*freeze_fs)(struct  super_block*) ;
int (*thaw_super)(struct  super_block*,enum freeze_holder) ;
int (*unfreeze_fs)(struct  super_block*) ;
int (*statfs)(struct  dentry*,struct  kstatfs*) ;
int (*remount_fs)(struct  super_block*,int*,char*) ;
void (*umount_begin)(struct  super_block*) ;
int (*show_options)(struct  seq_file*,struct  dentry*) ;
int (*show_devname)(struct  seq_file*,struct  dentry*) ;
int (*show_path)(struct  seq_file*,struct  dentry*) ;
int (*show_stats)(struct  seq_file*,struct  dentry*) ;
ssize_t (*quota_read)(struct  super_block*,int,char*,size_t,loff_t) ;
ssize_t (*quota_write)(struct  super_block*,int,char*,size_t,loff_t) ;
struct  dquot** (*get_dquots)(struct  inode*) ;
long (*nr_cached_objects)(struct  super_block*,struct  shrink_control*) ;
long (*free_cached_objects)(struct  super_block*,struct  shrink_control*) ;
void (*shutdown)(struct  super_block*) ;};
struct  kparam_array{
unsigned int max;
unsigned int elemsize;
unsigned int *num;
struct  kernel_param_ops *ops;
void *elem;};
struct  __kernel_timespec{
__kernel_time64_t tv_sec;
long long tv_nsec;};
struct  class{
char *name;
struct  attribute_group **class_groups;
struct  attribute_group **dev_groups;
int (*dev_uevent)(struct  device*,struct  kobj_uevent_env*) ;
char* (*devnode)(struct  device*,umode_t*) ;
void (*class_release)(struct  class*) ;
void (*dev_release)(struct  device*) ;
int (*shutdown_pre)(struct  device*) ;
struct  kobj_ns_type_operations *ns_type;
void* (*namespace)(struct  device*) ;
void (*get_ownership)(struct  device*,kuid_t*,kgid_t*) ;
struct  dev_pm_ops *pm;};
struct  fwnode_endpoint{
unsigned int port;
unsigned int id;
struct  fwnode_handle *local_fwnode;};
struct  kparam_string{
unsigned int maxlen;
char *string;};
struct  kernfs_node{
atomic_t count;
atomic_t active;
struct  kernfs_node *parent;
char *name;
struct  rb_node rb;
void *ns;
unsigned int hash;
union  {
struct  kernfs_elem_dir dir;
struct  kernfs_elem_symlink symlink;
struct  kernfs_elem_attr attr;} ;
void *priv;
u64 id;
unsigned short flags;
umode_t mode;
struct  kernfs_iattrs *iattr;};
struct  sched_class{
void (*enqueue_task)(struct  rq*,struct  task_struct*,int) ;
void (*dequeue_task)(struct  rq*,struct  task_struct*,int) ;
void (*yield_task)(struct  rq*) ;
bool (*yield_to_task)(struct  rq*,struct  task_struct*) ;
void (*check_preempt_curr)(struct  rq*,struct  task_struct*,int) ;
struct  task_struct* (*pick_next_task)(struct  rq*) ;
void (*put_prev_task)(struct  rq*,struct  task_struct*) ;
void (*set_next_task)(struct  rq*,struct  task_struct*,bool) ;
int (*balance)(struct  rq*,struct  task_struct*,struct  rq_flags*) ;
int (*select_task_rq)(struct  task_struct*,int,int) ;
struct  task_struct* (*pick_task)(struct  rq*) ;
void (*migrate_task_rq)(struct  task_struct*,int) ;
void (*task_woken)(struct  rq*,struct  task_struct*) ;
void (*set_cpus_allowed)(struct  task_struct*,struct  affinity_context*) ;
void (*rq_online)(struct  rq*) ;
void (*rq_offline)(struct  rq*) ;
struct  rq* (*find_lock_rq)(struct  task_struct*,struct  rq*) ;
void (*task_tick)(struct  rq*,struct  task_struct*,int) ;
void (*task_fork)(struct  task_struct*) ;
void (*task_dead)(struct  task_struct*) ;
void (*switched_from)(struct  rq*,struct  task_struct*) ;
void (*switched_to)(struct  rq*,struct  task_struct*) ;
void (*prio_changed)(struct  rq*,struct  task_struct*,int) ;
unsigned int (*get_rr_interval)(struct  rq*,struct  task_struct*) ;
void (*update_curr)(struct  rq*) ;
void (*task_change_group)(struct  task_struct*) ;};
struct  return_instance{
struct  uprobe *uprobe;
unsigned long func;
unsigned long stack;
unsigned long orig_ret_vaddr;
bool chained;
struct  return_instance *next;};
struct  quota_format_type{
int qf_fmt_id;
struct  quota_format_ops *qf_ops;
struct  module *qf_owner;
struct  quota_format_type *qf_next;};
struct  linux_binfmt{
struct  list_head lh;
struct  module *module;
int (*load_binary)(struct  linux_binprm*) ;
int (*load_shlib)(struct  file*) ;
int (*core_dump)(struct  coredump_params*) ;
unsigned long min_coredump;};
struct  balance_callback{
struct  balance_callback *next;
void (*func)(struct  rq*) ;};
struct  dev_pm_qos_request{
enum dev_pm_qos_req_type type;
union  {
struct  plist_node pnode;
struct  pm_qos_flags_request flr;
struct  freq_qos_request freq;} data;
struct  device *dev;};
struct  dquot{
struct  hlist_node dq_hash;
struct  list_head dq_inuse;
struct  list_head dq_free;
struct  list_head dq_dirty;
struct  mutex dq_lock;
spinlock_t dq_dqb_lock;
atomic_t dq_count;
struct  super_block *dq_sb;
struct  kqid dq_id;
loff_t dq_off;
unsigned long dq_flags;
struct  mem_dqblk dq_dqb;};
struct  poll_table_struct{
poll_queue_proc _qproc;
__poll_t _key;};
struct  vfsmount{
struct  dentry *mnt_root;
struct  super_block *mnt_sb;
int mnt_flags;
struct  mnt_idmap *mnt_idmap;};
struct  quota_format_ops{
int (*check_quota_file)(struct  super_block*,int) ;
int (*read_file_info)(struct  super_block*,int) ;
int (*write_file_info)(struct  super_block*,int) ;
int (*free_file_info)(struct  super_block*,int) ;
int (*read_dqblk)(struct  dquot*) ;
int (*commit_dqblk)(struct  dquot*) ;
int (*release_dqblk)(struct  dquot*) ;
int (*get_next_id)(struct  super_block*,struct  kqid*) ;};
struct  cpuidle_driver{
char *name;
struct  module *owner;
unsigned int bctimer:1;
struct  cpuidle_state states[10];
int state_count;
int safe_state_index;
struct  cpumask *cpumask;
char *governor;};
struct  dentry{
unsigned int d_flags;
seqcount_spinlock_t d_seq;
struct  hlist_bl_node d_hash;
struct  dentry *d_parent;
struct  qstr d_name;
struct  inode *d_inode;
unsigned char d_iname[32];
struct  lockref d_lockref;
struct  dentry_operations *d_op;
struct  super_block *d_sb;
unsigned long d_time;
void *d_fsdata;
union  {
struct  list_head d_lru;
wait_queue_head_t *d_wait;} ;
struct  list_head d_child;
struct  list_head d_subdirs;
union  {
struct  hlist_node d_alias;
struct  hlist_bl_node d_in_lookup_hash;
struct  callback_head d_rcu;} d_u;};
struct  device{
struct  kobject kobj;
struct  device *parent;
struct  device_private *p;
char *init_name;
struct  device_type *type;
struct  bus_type *bus;
struct  device_driver *driver;
void *platform_data;
void *driver_data;
struct  mutex mutex;
struct  dev_links_info links;
struct  dev_pm_info power;
struct  dev_pm_domain *pm_domain;
struct  dev_msi_info msi;
struct  dma_map_ops *dma_ops;
u64 *dma_mask;
u64 coherent_dma_mask;
u64 bus_dma_limit;
struct  bus_dma_region *dma_range_map;
struct  device_dma_parameters *dma_parms;
struct  list_head dma_pools;
struct  io_tlb_mem *dma_io_tlb_mem;
struct  dev_archdata archdata;
struct  device_node *of_node;
struct  fwnode_handle *fwnode;
int numa_node;
dev_t devt;
u32 id;
spinlock_t devres_lock;
struct  list_head devres_head;
struct  class *class;
struct  attribute_group **groups;
void (*release)(struct  device*) ;
struct  iommu_group *iommu_group;
struct  dev_iommu *iommu;
struct  device_physical_location *physical_location;
enum device_removable removable;
bool offline_disabled:1;
bool offline:1;
bool of_node_reused:1;
bool state_synced:1;
bool can_match:1;};
struct  cgroup_subsys{
struct  cgroup_subsys_state* (*css_alloc)(struct  cgroup_subsys_state*) ;
int (*css_online)(struct  cgroup_subsys_state*) ;
void (*css_offline)(struct  cgroup_subsys_state*) ;
void (*css_released)(struct  cgroup_subsys_state*) ;
void (*css_free)(struct  cgroup_subsys_state*) ;
void (*css_reset)(struct  cgroup_subsys_state*) ;
void (*css_rstat_flush)(struct  cgroup_subsys_state*,int) ;
int (*css_extra_stat_show)(struct  seq_file*,struct  cgroup_subsys_state*) ;
int (*css_local_stat_show)(struct  seq_file*,struct  cgroup_subsys_state*) ;
int (*can_attach)(struct  cgroup_taskset*) ;
void (*cancel_attach)(struct  cgroup_taskset*) ;
void (*attach)(struct  cgroup_taskset*) ;
void (*post_attach)() ;
int (*can_fork)(struct  task_struct*,struct  css_set*) ;
void (*cancel_fork)(struct  task_struct*,struct  css_set*) ;
void (*fork)(struct  task_struct*) ;
void (*exit)(struct  task_struct*) ;
void (*release)(struct  task_struct*) ;
void (*bind)(struct  cgroup_subsys_state*) ;
bool early_init:1;
bool implicit_on_dfl:1;
bool threaded:1;
int id;
char *name;
char *legacy_name;
struct  cgroup_root *root;
struct  idr css_idr;
struct  list_head cfts;
struct  cftype *dfl_cftypes;
struct  cftype *legacy_cftypes;
unsigned int depends_on;};
struct  notifier_block{
notifier_fn_t notifier_call;
struct  notifier_block *next;
int priority;};
struct  key_tag{
struct  callback_head rcu;
refcount_t usage;
bool removed;};
struct  orc_entry{
s16 sp_offset;
s16 bp_offset;
unsigned int sp_reg:4;
unsigned int bp_reg:4;
unsigned int type:3;
unsigned int signal:1;};
struct  old_timespec32{
old_time32_t tv_sec;
s32 tv_nsec;};
struct  rseq{
__u32 cpu_id_start;
__u32 cpu_id;
__u64 rseq_cs;
__u32 flags;
__u32 node_id;
__u32 mm_cid;
char end[6];};
struct  key{
refcount_t usage;
key_serial_t serial;
union  {
struct  list_head graveyard_link;
struct  rb_node serial_node;} ;
struct  rw_semaphore sem;
struct  key_user *user;
void *security;
union  {
time64_t expiry;
time64_t revoked_at;} ;
time64_t last_used_at;
kuid_t uid;
kgid_t gid;
key_perm_t perm;
unsigned short quotalen;
unsigned short datalen;
short state;
unsigned long flags;
union  {
struct  keyring_index_key index_key;
struct  {
unsigned long hash;
unsigned long len_desc;
struct  key_type *type;
struct  key_tag *domain_tag;
char *description;} ;} ;
union  {
union  key_payload payload;
struct  {
struct  list_head name_link;
struct  assoc_array keys;} ;} ;
struct  key_restriction *restrict_link;};
struct  device_driver{
char *name;
struct  bus_type *bus;
struct  module *owner;
char *mod_name;
bool suppress_bind_attrs;
enum probe_type probe_type;
struct  of_device_id *of_match_table;
struct  acpi_device_id *acpi_match_table;
int (*probe)(struct  device*) ;
void (*sync_state)(struct  device*) ;
int (*remove)(struct  device*) ;
void (*shutdown)(struct  device*) ;
int (*suspend)(struct  device*,pm_message_t) ;
int (*resume)(struct  device*) ;
struct  attribute_group **groups;
struct  attribute_group **dev_groups;
struct  dev_pm_ops *pm;
void (*coredump)(struct  device*) ;
struct  driver_private *p;};
struct  mm_cid{
u64 time;
int cid;};
struct  group_info{
atomic_t usage;
int ngroups;
kgid_t gid[];};
struct  kstat{
u32 result_mask;
umode_t mode;
unsigned int nlink;
uint32_t blksize;
u64 attributes;
u64 attributes_mask;
u64 ino;
dev_t dev;
dev_t rdev;
kuid_t uid;
kgid_t gid;
loff_t size;
struct  timespec64 atime;
struct  timespec64 mtime;
struct  timespec64 ctime;
struct  timespec64 btime;
u64 blocks;
u64 mnt_id;
u32 dio_mem_align;
u32 dio_offset_align;
u64 change_cookie;};
struct  uprobe_task{
enum uprobe_task_state state;
union  {
struct  {
struct  arch_uprobe_task autask;
unsigned long vaddr;} ;
struct  {
struct  callback_head dup_xol_work;
unsigned long dup_xol_addr;} ;} ;
struct  uprobe *active_uprobe;
unsigned long xol_vaddr;
struct  return_instance *return_instances;
unsigned int depth;};
struct  ctl_table_poll{
atomic_t event;
wait_queue_head_t wait;};
struct  readahead_control{
struct  file *file;
struct  address_space *mapping;
struct  file_ra_state *ra;
unsigned long _index;
unsigned int _nr_pages;
unsigned int _batch_count;
bool _workingset;
unsigned long _pflags;};
struct  pid{
refcount_t count;
unsigned int level;
spinlock_t lock;
struct  hlist_head tasks[4];
struct  hlist_head inodes;
wait_queue_head_t wait_pidfd;
struct  callback_head rcu;
struct  upid numbers[];};
struct  dev_pm_qos{
struct  pm_qos_constraints resume_latency;
struct  pm_qos_constraints latency_tolerance;
struct  freq_constraints freq;
struct  pm_qos_flags flags;
struct  dev_pm_qos_request *resume_latency_req;
struct  dev_pm_qos_request *latency_tolerance_req;
struct  dev_pm_qos_request *flags_req;};
struct  kernel_param_ops{
unsigned int flags;
int (*set)(char*,struct  kernel_param*) ;
int (*get)(char*,struct  kernel_param*) ;
void (*free)(void*) ;};
struct  bug_entry{
int bug_addr_disp;
int file_disp;
unsigned short line;
unsigned short flags;};
struct  device_physical_location{
enum device_physical_location_panel panel;
enum device_physical_location_vertical_position vertical_position;
enum device_physical_location_horizontal_position horizontal_position;
bool dock;
bool lid;};
struct  pt_regs{
unsigned long r15;
unsigned long r14;
unsigned long r13;
unsigned long r12;
unsigned long bp;
unsigned long bx;
unsigned long r11;
unsigned long r10;
unsigned long r9;
unsigned long r8;
unsigned long ax;
unsigned long cx;
unsigned long dx;
unsigned long si;
unsigned long di;
unsigned long orig_ax;
unsigned long ip;
unsigned long cs;
unsigned long flags;
unsigned long sp;
unsigned long ss;};
struct  perf_addr_filter_range{
unsigned long start;
unsigned long size;};
struct  perf_cgroup_info{
u64 time;
u64 timestamp;
u64 timeoffset;
int active;};
struct  dir_context{
filldir_t actor;
loff_t pos;};
struct  cgroup_rstat_cpu{
struct  u64_stats_sync bsync;
struct  cgroup_base_stat bstat;
struct  cgroup_base_stat last_bstat;
struct  cgroup_base_stat subtree_bstat;
struct  cgroup_base_stat last_subtree_bstat;
struct  cgroup *updated_children;
struct  cgroup *updated_next;};
struct  pid_namespace{
struct  idr idr;
struct  callback_head rcu;
unsigned int pid_allocated;
struct  task_struct *child_reaper;
struct  kmem_cache *pid_cachep;
unsigned int level;
struct  pid_namespace *parent;
struct  fs_pin *bacct;
struct  user_namespace *user_ns;
struct  ucounts *ucounts;
int reboot;
struct  ns_common ns;
int memfd_noexec_scope;};
struct  sched_group_capacity{
atomic_t ref;
unsigned long capacity;
unsigned long min_capacity;
unsigned long max_capacity;
unsigned long next_update;
int imbalance;
unsigned long cpumask[1];};
struct  file_system_type{
char *name;
int fs_flags;
int (*init_fs_context)(struct  fs_context*) ;
struct  fs_parameter_spec *parameters;
struct  dentry* (*mount)(struct  file_system_type*,int,char*,void*) ;
void (*kill_sb)(struct  super_block*) ;
struct  module *owner;
struct  file_system_type *next;
struct  hlist_head fs_supers;
struct  lock_class_key s_lock_key;
struct  lock_class_key s_umount_key;
struct  lock_class_key s_vfs_rename_key;
struct  lock_class_key s_writers_key[3];
struct  lock_class_key i_lock_key;
struct  lock_class_key i_mutex_key;
struct  lock_class_key invalidate_lock_key;
struct  lock_class_key i_mutex_dir_key;};
struct  module_attribute{
struct  attribute attr;
ssize_t (*show)(struct  module_attribute*,struct  module_kobject*,char*) ;
ssize_t (*store)(struct  module_attribute*,struct  module_kobject*,char*,size_t) ;
void (*setup)(struct  module*,char*) ;
int (*test)(struct  module*) ;
void (*free)(struct  module*) ;};
struct  inode{
umode_t i_mode;
unsigned short i_opflags;
kuid_t i_uid;
kgid_t i_gid;
unsigned int i_flags;
struct  posix_acl *i_acl;
struct  posix_acl *i_default_acl;
struct  inode_operations *i_op;
struct  super_block *i_sb;
struct  address_space *i_mapping;
void *i_security;
unsigned long i_ino;
union  {
unsigned int i_nlink;
unsigned int __i_nlink;} ;
dev_t i_rdev;
loff_t i_size;
struct  timespec64 i_atime;
struct  timespec64 i_mtime;
struct  timespec64 __i_ctime;
spinlock_t i_lock;
unsigned short i_bytes;
u8 i_blkbits;
u8 i_write_hint;
blkcnt_t i_blocks;
unsigned long i_state;
struct  rw_semaphore i_rwsem;
unsigned long dirtied_when;
unsigned long dirtied_time_when;
struct  hlist_node i_hash;
struct  list_head i_io_list;
struct  list_head i_lru;
struct  list_head i_sb_list;
struct  list_head i_wb_list;
union  {
struct  hlist_head i_dentry;
struct  callback_head i_rcu;} ;
atomic64_t i_version;
atomic64_t i_sequence;
atomic_t i_count;
atomic_t i_dio_count;
atomic_t i_writecount;
atomic_t i_readcount;
union  {
struct  file_operations *i_fop;
void (*free_inode)(struct  inode*) ;} ;
struct  file_lock_context *i_flctx;
struct  address_space i_data;
struct  list_head i_devices;
union  {
struct  pipe_inode_info *i_pipe;
struct  cdev *i_cdev;
char *i_link;
unsigned int i_dir_seq;} ;
__u32 i_generation;
__u32 i_fsnotify_mask;
struct  fsnotify_mark_connector *i_fsnotify_marks;
void *i_private;};
struct  vm_area_struct{
union  {
struct  {
unsigned long vm_start;
unsigned long vm_end;} ;
struct  callback_head vm_rcu;} ;
struct  mm_struct *vm_mm;
pgprot_t vm_page_prot;
union  {
vm_flags_t vm_flags;
vm_flags_t __vm_flags;} ;
int vm_lock_seq;
struct  vma_lock *vm_lock;
bool detached;
struct  {
struct  rb_node rb;
unsigned long rb_subtree_last;} shared;
struct  list_head anon_vma_chain;
struct  anon_vma *anon_vma;
struct  vm_operations_struct *vm_ops;
unsigned long vm_pgoff;
struct  file *vm_file;
void *vm_private_data;
atomic_long_t swap_readahead_info;
struct  mempolicy *vm_policy;
struct  vm_userfaultfd_ctx vm_userfaultfd_ctx;};
struct  folio{
union  {
struct  {
unsigned long flags;
union  {
struct  list_head lru;
struct  {
void *__filler;
unsigned int mlock_count;} ;} ;
struct  address_space *mapping;
unsigned long index;
union  {
void *private;
swp_entry_t swap;} ;
atomic_t _mapcount;
atomic_t _refcount;} ;
struct  page page;} ;
union  {
struct  {
unsigned long _flags_1;
unsigned long _head_1;
unsigned long _folio_avail;
atomic_t _entire_mapcount;
atomic_t _nr_pages_mapped;
atomic_t _pincount;
unsigned int _folio_nr_pages;} ;
struct  page __page_1;} ;
union  {
struct  {
unsigned long _flags_2;
unsigned long _head_2;
void *_hugetlb_subpool;
void *_hugetlb_cgroup;
void *_hugetlb_cgroup_rsvd;
void *_hugetlb_hwpoison;} ;
struct  {
unsigned long _flags_2a;
unsigned long _head_2a;
struct  list_head _deferred_list;} ;
struct  page __page_2;} ;};
struct  perf_event{
struct  list_head event_entry;
struct  list_head sibling_list;
struct  list_head active_list;
struct  rb_node group_node;
u64 group_index;
struct  list_head migrate_entry;
struct  hlist_node hlist_entry;
struct  list_head active_entry;
int nr_siblings;
int event_caps;
int group_caps;
unsigned int group_generation;
struct  perf_event *group_leader;
struct  pmu *pmu;
void *pmu_private;
enum perf_event_state state;
unsigned int attach_state;
local64_t count;
atomic64_t child_count;
u64 total_time_enabled;
u64 total_time_running;
u64 tstamp;
struct  perf_event_attr attr;
u16 header_size;
u16 id_header_size;
u16 read_size;
struct  hw_perf_event hw;
struct  perf_event_context *ctx;
struct  perf_event_pmu_context *pmu_ctx;
atomic_long_t refcount;
atomic64_t child_total_time_enabled;
atomic64_t child_total_time_running;
struct  mutex child_mutex;
struct  list_head child_list;
struct  perf_event *parent;
int oncpu;
int cpu;
struct  list_head owner_entry;
struct  task_struct *owner;
struct  mutex mmap_mutex;
atomic_t mmap_count;
struct  perf_buffer *rb;
struct  list_head rb_entry;
unsigned long rcu_batches;
int rcu_pending;
wait_queue_head_t waitq;
struct  fasync_struct *fasync;
unsigned int pending_wakeup;
unsigned int pending_kill;
unsigned int pending_disable;
unsigned int pending_sigtrap;
unsigned long pending_addr;
struct  irq_work pending_irq;
struct  callback_head pending_task;
unsigned int pending_work;
atomic_t event_limit;
struct  perf_addr_filters_head addr_filters;
struct  perf_addr_filter_range *addr_filter_ranges;
unsigned long addr_filters_gen;
struct  perf_event *aux_event;
void (*destroy)(struct  perf_event*) ;
struct  callback_head callback_head;
struct  pid_namespace *ns;
u64 id;
atomic64_t lost_samples;
u64 (*clock)() ;
perf_overflow_handler_t overflow_handler;
void *overflow_handler_context;
struct  trace_event_call *tp_event;
struct  event_filter *filter;
struct  perf_cgroup *cgrp;
void *security;
struct  list_head sb_list;
__u32 orig_type;};
struct  dquot_operations{
int (*write_dquot)(struct  dquot*) ;
struct  dquot* (*alloc_dquot)(struct  super_block*,int) ;
void (*destroy_dquot)(struct  dquot*) ;
int (*acquire_dquot)(struct  dquot*) ;
int (*release_dquot)(struct  dquot*) ;
int (*mark_dirty)(struct  dquot*) ;
int (*write_info)(struct  super_block*,int) ;
qsize_t* (*get_reserved_space)(struct  inode*) ;
int (*get_projid)(struct  inode*,kprojid_t*) ;
int (*get_inode_usage)(struct  inode*,qsize_t*) ;
int (*get_next_id)(struct  super_block*,struct  kqid*) ;};
struct  cftype{
char name[6];
unsigned long private;
size_t max_write_len;
unsigned int flags;
unsigned int file_offset;
struct  cgroup_subsys *ss;
struct  list_head node;
struct  kernfs_ops *kf_ops;
int (*open)(struct  kernfs_open_file*) ;
void (*release)(struct  kernfs_open_file*) ;
u64 (*read_u64)(struct  cgroup_subsys_state*,struct  cftype*) ;
s64 (*read_s64)(struct  cgroup_subsys_state*,struct  cftype*) ;
int (*seq_show)(struct  seq_file*,void*) ;
void* (*seq_start)(struct  seq_file*,loff_t*) ;
void* (*seq_next)(struct  seq_file*,void*,loff_t*) ;
void (*seq_stop)(struct  seq_file*,void*) ;
int (*write_u64)(struct  cgroup_subsys_state*,struct  cftype*,u64) ;
int (*write_s64)(struct  cgroup_subsys_state*,struct  cftype*,s64) ;
ssize_t (*write)(struct  kernfs_open_file*,char*,size_t,loff_t) ;
__poll_t (*poll)(struct  kernfs_open_file*,struct  poll_table_struct*) ;};
struct  list_lru_node{
spinlock_t lock;
struct  list_lru_one lru;
long nr_items;};
enum uclamp_id{UCLAMP_MIN,UCLAMP_MAX,UCLAMP_CNT};
struct  task_struct{
struct  thread_info thread_info;
unsigned int __state;
void *stack;
refcount_t usage;
unsigned int flags;
unsigned int ptrace;
int on_cpu;
struct  __call_single_node wake_entry;
unsigned int wakee_flips;
unsigned long wakee_flip_decay_ts;
struct  task_struct *last_wakee;
int recent_used_cpu;
int wake_cpu;
int on_rq;
int prio;
int static_prio;
int normal_prio;
unsigned int rt_priority;
struct  sched_entity se;
struct  sched_rt_entity rt;
struct  sched_dl_entity dl;
struct  sched_class *sched_class;
struct  task_group *sched_task_group;
struct  sched_statistics stats;
unsigned int btrace_seq;
unsigned int policy;
int nr_cpus_allowed;
cpumask_t *cpus_ptr;
cpumask_t *user_cpus_ptr;
cpumask_t cpus_mask;
void *migration_pending;
unsigned short migration_disabled;
unsigned short migration_flags;
int rcu_read_lock_nesting;
union  rcu_special rcu_read_unlock_special;
struct  list_head rcu_node_entry;
struct  rcu_node *rcu_blocked_node;
unsigned long rcu_tasks_nvcsw;
u8 rcu_tasks_holdout;
u8 rcu_tasks_idx;
int rcu_tasks_idle_cpu;
struct  list_head rcu_tasks_holdout_list;
struct  sched_info sched_info;
struct  list_head tasks;
struct  plist_node pushable_tasks;
struct  rb_node pushable_dl_tasks;
struct  mm_struct *mm;
struct  mm_struct *active_mm;
int exit_state;
int exit_code;
int exit_signal;
int pdeath_signal;
unsigned long jobctl;
unsigned int personality;
unsigned int sched_reset_on_fork:1;
unsigned int sched_contributes_to_load:1;
unsigned int sched_migrated:1;
unsigned int :0;
unsigned int sched_remote_wakeup:1;
unsigned int in_execve:1;
unsigned int in_iowait:1;
unsigned int restore_sigmask:1;
unsigned int no_cgroup_migration:1;
unsigned int frozen:1;
unsigned int use_memdelay:1;
unsigned int in_eventfd:1;
unsigned int reported_split_lock:1;
unsigned int in_thrashing:1;
unsigned long atomic_flags;
struct  restart_block restart_block;
pid_t pid;
pid_t tgid;
unsigned long stack_canary;
struct  task_struct *real_parent;
struct  task_struct *parent;
struct  list_head children;
struct  list_head sibling;
struct  task_struct *group_leader;
struct  list_head ptraced;
struct  list_head ptrace_entry;
struct  pid *thread_pid;
struct  hlist_node pid_links[4];
struct  list_head thread_group;
struct  list_head thread_node;
struct  completion *vfork_done;
int *set_child_tid;
int *clear_child_tid;
void *worker_private;
u64 utime;
u64 stime;
u64 gtime;
struct  prev_cputime prev_cputime;
unsigned long nvcsw;
unsigned long nivcsw;
u64 start_time;
u64 start_boottime;
unsigned long min_flt;
unsigned long maj_flt;
struct  posix_cputimers posix_cputimers;
struct  posix_cputimers_work posix_cputimers_work;
struct  cred *ptracer_cred;
struct  cred *real_cred;
struct  cred *cred;
struct  key *cached_requested_key;
char comm[6];
struct  nameidata *nameidata;
struct  sysv_sem sysvsem;
struct  sysv_shm sysvshm;
struct  fs_struct *fs;
struct  files_struct *files;
struct  io_uring_task *io_uring;
struct  nsproxy *nsproxy;
struct  signal_struct *signal;
struct  sighand_struct *sighand;
sigset_t blocked;
sigset_t real_blocked;
sigset_t saved_sigmask;
struct  sigpending pending;
unsigned long sas_ss_sp;
size_t sas_ss_size;
unsigned int sas_ss_flags;
struct  callback_head *task_works;
struct  audit_context *audit_context;
kuid_t loginuid;
unsigned int sessionid;
struct  seccomp seccomp;
struct  syscall_user_dispatch syscall_dispatch;
u64 parent_exec_id;
u64 self_exec_id;
spinlock_t alloc_lock;
raw_spinlock_t pi_lock;
struct  wake_q_node wake_q;
struct  rb_root_cached pi_waiters;
struct  task_struct *pi_top_task;
struct  rt_mutex_waiter *pi_blocked_on;
void *journal_info;
struct  bio_list *bio_list;
struct  blk_plug *plug;
struct  reclaim_state *reclaim_state;
struct  io_context *io_context;
struct  capture_control *capture_control;
unsigned long ptrace_message;
kernel_siginfo_t *last_siginfo;
struct  task_io_accounting ioac;
u64 acct_rss_mem1;
u64 acct_vm_mem1;
u64 acct_timexpd;
nodemask_t mems_allowed;
seqcount_spinlock_t mems_allowed_seq;
int cpuset_mem_spread_rotor;
int cpuset_slab_spread_rotor;
struct  css_set *cgroups;
struct  list_head cg_list;
struct  robust_list_head *robust_list;
struct  compat_robust_list_head *compat_robust_list;
struct  list_head pi_state_list;
struct  futex_pi_state *pi_state_cache;
struct  mutex futex_exit_mutex;
unsigned int futex_state;
struct  perf_event_context *perf_event_ctxp;
struct  mutex perf_event_mutex;
struct  list_head perf_event_list;
struct  mempolicy *mempolicy;
short il_prev;
short pref_node_fork;
struct  rseq *rseq;
u32 rseq_len;
u32 rseq_sig;
unsigned long rseq_event_mask;
int mm_cid;
int last_mm_cid;
int migrate_from_cpu;
int mm_cid_active;
struct  callback_head cid_work;
struct  tlbflush_unmap_batch tlb_ubc;
struct  pipe_inode_info *splice_pipe;
struct  page_frag task_frag;
struct  task_delay_info *delays;
int nr_dirtied;
int nr_dirtied_pause;
unsigned long dirty_paused_when;
u64 timer_slack_ns;
u64 default_timer_slack_ns;
unsigned long trace_recursion;
struct  gendisk *throttle_disk;
struct  uprobe_task *utask;
struct  kmap_ctrl kmap_ctrl;
struct  callback_head rcu;
refcount_t rcu_users;
int pagefault_disabled;
struct  task_struct *oom_reaper_list;
struct  timer_list oom_reaper_timer;
struct  vm_struct *stack_vm_area;
refcount_t stack_refcount;
void *security;
void *mce_vaddr;
__u64 mce_kflags;
u64 mce_addr;
__u64 mce_ripv:1;
__u64 mce_whole_page:1;
__u64 __mce_reserved:62;
struct  callback_head mce_kill_me;
int mce_count;
struct  llist_head kretprobe_instances;
struct  llist_head rethooks;
struct  callback_head l1d_flush_kill;
struct  thread_struct thread;};
struct  srcu_node{
spinlock_t lock;
unsigned long srcu_have_cbs[1];
unsigned long srcu_data_have_cbs[1];
unsigned long srcu_gp_seq_needed_exp;
struct  srcu_node *srcu_parent;
int grplo;
int grphi;};
struct  trace_event_class{
char *system;
void *probe;
void *perf_probe;
int (*reg)(struct  trace_event_call*,enum trace_reg,void*) ;
struct  trace_event_fields *fields_array;
struct  list_head* (*get_fields)(struct  trace_event_call*) ;
struct  list_head fields;
int (*raw_init)(struct  trace_event_call*) ;};
struct  static_call_key{
void *func;
union  {
unsigned long type;
struct  static_call_mod *mods;
struct  static_call_site *sites;} ;};
struct  ctl_table_root{
struct  ctl_table_set default_set;
struct  ctl_table_set* (*lookup)(struct  ctl_table_root*) ;
void (*set_ownership)(struct  ctl_table_header*,struct  ctl_table*,kuid_t*,kgid_t*) ;
int (*permissions)(struct  ctl_table_header*,struct  ctl_table*) ;};
struct  qc_dqblk{
int d_fieldmask;
u64 d_spc_hardlimit;
u64 d_spc_softlimit;
u64 d_ino_hardlimit;
u64 d_ino_softlimit;
u64 d_space;
u64 d_ino_count;
s64 d_ino_timer;
s64 d_spc_timer;
int d_ino_warns;
int d_spc_warns;
u64 d_rt_spc_hardlimit;
u64 d_rt_spc_softlimit;
u64 d_rt_space;
s64 d_rt_spc_timer;
int d_rt_spc_warns;};
struct  perf_output_handle{
struct  perf_event *event;
struct  perf_buffer *rb;
unsigned long wakeup;
unsigned long size;
u64 aux_flags;
union  {
void *addr;
unsigned long head;} ;
int page;};
struct  fwnode_operations{
struct  fwnode_handle* (*get)(struct  fwnode_handle*) ;
void (*put)(struct  fwnode_handle*) ;
bool (*device_is_available)(struct  fwnode_handle*) ;
void* (*device_get_match_data)(struct  fwnode_handle*,struct  device*) ;
bool (*device_dma_supported)(struct  fwnode_handle*) ;
enum dev_dma_attr (*device_get_dma_attr)(struct  fwnode_handle*) ;
bool (*property_present)(struct  fwnode_handle*,char*) ;
int (*property_read_int_array)(struct  fwnode_handle*,char*,unsigned int,void*,size_t) ;
int (*property_read_string_array)(struct  fwnode_handle*,char*,char**,size_t) ;
char* (*get_name)(struct  fwnode_handle*) ;
char* (*get_name_prefix)(struct  fwnode_handle*) ;
struct  fwnode_handle* (*get_parent)(struct  fwnode_handle*) ;
struct  fwnode_handle* (*get_next_child_node)(struct  fwnode_handle*,struct  fwnode_handle*) ;
struct  fwnode_handle* (*get_named_child_node)(struct  fwnode_handle*,char*) ;
int (*get_reference_args)(struct  fwnode_handle*,char*,char*,unsigned int,unsigned int,struct  fwnode_reference_args*) ;
struct  fwnode_handle* (*graph_get_next_endpoint)(struct  fwnode_handle*,struct  fwnode_handle*) ;
struct  fwnode_handle* (*graph_get_remote_endpoint)(struct  fwnode_handle*) ;
struct  fwnode_handle* (*graph_get_port_parent)(struct  fwnode_handle*) ;
int (*graph_parse_endpoint)(struct  fwnode_handle*,struct  fwnode_endpoint*) ;
void* (*iomap)(struct  fwnode_handle*,int) ;
int (*irq_get)(struct  fwnode_handle*,unsigned int) ;
int (*add_links)(struct  fwnode_handle*) ;};
struct  kernfs_open_file{
struct  kernfs_node *kn;
struct  file *file;
struct  seq_file *seq_file;
void *priv;
struct  mutex mutex;
struct  mutex prealloc_mutex;
int event;
struct  list_head list;
char *prealloc_buf;
size_t atomic_write_len;
bool mmapped:1;
bool released:1;
struct  vm_operations_struct *vm_ops;};
struct  fasync_struct{
rwlock_t fa_lock;
int magic;
int fa_fd;
struct  fasync_struct *fa_next;
struct  file *fa_file;
struct  callback_head fa_rcu;};
struct  dev_pagemap_ops{
void (*page_free)(struct  page*) ;
vm_fault_t (*migrate_to_ram)(struct  vm_fault*) ;
int (*memory_failure)(struct  dev_pagemap*,unsigned long,unsigned long,int) ;};
struct  shrink_control{
gfp_t gfp_mask;
int nid;
unsigned long nr_to_scan;
unsigned long nr_scanned;
struct  mem_cgroup *memcg;};
struct  file_operations{
struct  module *owner;
loff_t (*llseek)(struct  file*,loff_t,int) ;
ssize_t (*read)(struct  file*,char*,size_t,loff_t*) ;
ssize_t (*write)(struct  file*,char*,size_t,loff_t*) ;
ssize_t (*read_iter)(struct  kiocb*,struct  iov_iter*) ;
ssize_t (*write_iter)(struct  kiocb*,struct  iov_iter*) ;
int (*iopoll)(struct  kiocb*,struct  io_comp_batch*,unsigned int) ;
int (*iterate_shared)(struct  file*,struct  dir_context*) ;
__poll_t (*poll)(struct  file*,struct  poll_table_struct*) ;
long (*unlocked_ioctl)(struct  file*,unsigned int,unsigned long) ;
long (*compat_ioctl)(struct  file*,unsigned int,unsigned long) ;
int (*mmap)(struct  file*,struct  vm_area_struct*) ;
unsigned long mmap_supported_flags;
int (*open)(struct  inode*,struct  file*) ;
int (*flush)(struct  file*,fl_owner_t) ;
int (*release)(struct  inode*,struct  file*) ;
int (*fsync)(struct  file*,loff_t,loff_t,int) ;
int (*fasync)(int,struct  file*,int) ;
int (*lock)(struct  file*,int,struct  file_lock*) ;
unsigned long (*get_unmapped_area)(struct  file*,unsigned long,unsigned long,unsigned long,unsigned long) ;
int (*check_flags)(int) ;
int (*flock)(struct  file*,int,struct  file_lock*) ;
ssize_t (*splice_write)(struct  pipe_inode_info*,struct  file*,loff_t*,size_t,unsigned int) ;
ssize_t (*splice_read)(struct  file*,loff_t*,struct  pipe_inode_info*,size_t,unsigned int) ;
void (*splice_eof)(struct  file*) ;
int (*setlease)(struct  file*,int,struct  file_lock**,void**) ;
long (*fallocate)(struct  file*,int,loff_t,loff_t) ;
void (*show_fdinfo)(struct  seq_file*,struct  file*) ;
ssize_t (*copy_file_range)(struct  file*,loff_t,struct  file*,loff_t,size_t,unsigned int) ;
loff_t (*remap_file_range)(struct  file*,loff_t,struct  file*,loff_t,loff_t,unsigned int) ;
int (*fadvise)(struct  file*,loff_t,loff_t,int) ;
int (*uring_cmd)(struct  io_uring_cmd*,unsigned int) ;
int (*uring_cmd_iopoll)(struct  io_uring_cmd*,struct  io_comp_batch*,unsigned int) ;};
struct  module{
enum module_state state;
struct  list_head list;
char name[6];
struct  module_kobject mkobj;
struct  module_attribute *modinfo_attrs;
char *version;
char *srcversion;
struct  kobject *holders_dir;
struct  kernel_symbol *syms;
s32 *crcs;
unsigned int num_syms;
struct  mutex param_lock;
struct  kernel_param *kp;
unsigned int num_kp;
unsigned int num_gpl_syms;
struct  kernel_symbol *gpl_syms;
s32 *gpl_crcs;
bool using_gplonly_symbols;
bool async_probe_requested;
unsigned int num_exentries;
struct  exception_table_entry *extable;
int (*init)() ;
struct  module_memory mem[7];
struct  mod_arch_specific arch;
unsigned long taints;
unsigned int num_bugs;
struct  list_head bug_list;
struct  bug_entry *bug_table;
struct  mod_kallsyms *kallsyms;
struct  mod_kallsyms core_kallsyms;
struct  module_sect_attrs *sect_attrs;
struct  module_notes_attrs *notes_attrs;
char *args;
void *percpu;
unsigned int percpu_size;
void *noinstr_text_start;
unsigned int noinstr_text_size;
unsigned int num_tracepoints;
tracepoint_ptr_t *tracepoints_ptrs;
unsigned int num_srcu_structs;
struct  srcu_struct **srcu_struct_ptrs;
struct  jump_entry *jump_entries;
unsigned int num_jump_entries;
unsigned int num_trace_bprintk_fmt;
char **trace_bprintk_fmt_start;
struct  trace_event_call **trace_events;
unsigned int num_trace_events;
struct  trace_eval_map **trace_evals;
unsigned int num_trace_evals;
void *kprobes_text_start;
unsigned int kprobes_text_size;
unsigned long *kprobe_blacklist;
unsigned int num_kprobe_blacklist;
int num_static_call_sites;
struct  static_call_site *static_call_sites;
struct  list_head source_list;
struct  list_head target_list;
void (*exit)() ;
atomic_t refcnt;};
struct  vdso_image{
void *data;
unsigned long size;
unsigned long alt;
unsigned long alt_len;
unsigned long extable_base;
unsigned long extable_len;
void *extable;
long sym_vvar_start;
long sym_vvar_page;
long sym_pvclock_page;
long sym_hvclock_page;
long sym_timens_page;
long sym_VDSO32_NOTE_MASK;
long sym___kernel_sigreturn;
long sym___kernel_rt_sigreturn;
long sym___kernel_vsyscall;
long sym_int80_landing_pad;
long sym_vdso32_sigreturn_landing_pad;
long sym_vdso32_rt_sigreturn_landing_pad;};
struct  sched_group{
struct  sched_group *next;
atomic_t ref;
unsigned int group_weight;
unsigned int cores;
struct  sched_group_capacity *sgc;
int asym_prefer_cpu;
int flags;
unsigned long cpumask[1];};
struct  css_set{
struct  cgroup_subsys_state *subsys[14];
refcount_t refcount;
struct  css_set *dom_cset;
struct  cgroup *dfl_cgrp;
int nr_tasks;
struct  list_head tasks;
struct  list_head mg_tasks;
struct  list_head dying_tasks;
struct  list_head task_iters;
struct  list_head e_cset_node[100];
struct  list_head threaded_csets;
struct  list_head threaded_csets_node;
struct  hlist_node hlist;
struct  list_head cgrp_links;
struct  list_head mg_src_preload_node;
struct  list_head mg_dst_preload_node;
struct  list_head mg_node;
struct  cgroup *mg_src_cgrp;
struct  cgroup *mg_dst_cgrp;
struct  css_set *mg_dst_cset;
bool dead;
struct  callback_head callback_head;};
struct  perf_domain{
struct  em_perf_domain *em_pd;
struct  perf_domain *next;
struct  callback_head rcu;};
struct  wait_page_queue{
struct  folio *folio;
int bit_nr;
wait_queue_entry_t wait;};
struct  kset{
struct  list_head list;
spinlock_t list_lock;
struct  kobject kobj;
struct  kset_uevent_ops *uevent_ops;};
struct  kernel_param{
char *name;
struct  module *mod;
struct  kernel_param_ops *ops;
u16 perm;
s8 level;
u8 flags;
union  {
void *arg;
struct  kparam_string *str;
struct  kparam_array *arr;} ;};
struct  nsproxy{
refcount_t count;
struct  uts_namespace *uts_ns;
struct  ipc_namespace *ipc_ns;
struct  mnt_namespace *mnt_ns;
struct  pid_namespace *pid_ns_for_children;
struct  net *net_ns;
struct  time_namespace *time_ns;
struct  time_namespace *time_ns_for_children;
struct  cgroup_namespace *cgroup_ns;};
struct  cpuidle_device{
unsigned int registered:1;
unsigned int enabled:1;
unsigned int poll_time_limit:1;
unsigned int cpu;
ktime_t next_hrtimer;
int last_state_idx;
u64 last_residency_ns;
u64 poll_limit_ns;
u64 forced_idle_latency_limit_ns;
struct  cpuidle_state_usage states_usage[10];
struct  cpuidle_state_kobj *kobjs[10];
struct  cpuidle_driver_kobj *kobj_driver;
struct  cpuidle_device_kobj *kobj_dev;
struct  list_head device_list;};
struct  rq{
raw_spinlock_t __lock;
unsigned int nr_running;
unsigned long last_blocked_load_update_tick;
unsigned int has_blocked_load;
call_single_data_t nohz_csd;
unsigned int nohz_tick_stopped;
atomic_t nohz_flags;
unsigned int ttwu_pending;
u64 nr_switches;
struct  cfs_rq cfs;
struct  rt_rq rt;
struct  dl_rq dl;
struct  list_head leaf_cfs_rq_list;
struct  list_head *tmp_alone_branch;
unsigned int nr_uninterruptible;
struct  task_struct *curr;
struct  task_struct *idle;
struct  task_struct *stop;
unsigned long next_balance;
struct  mm_struct *prev_mm;
unsigned int clock_update_flags;
u64 clock;
u64 clock_task;
u64 clock_pelt;
unsigned long lost_idle_time;
u64 clock_pelt_idle;
u64 clock_idle;
atomic_t nr_iowait;
int membarrier_state;
struct  root_domain *rd;
struct  sched_domain *sd;
unsigned long cpu_capacity;
unsigned long cpu_capacity_orig;
struct  balance_callback *balance_callback;
unsigned char nohz_idle_balance;
unsigned char idle_balance;
unsigned long misfit_task_load;
int active_balance;
int push_cpu;
struct  cpu_stop_work active_balance_work;
int cpu;
int online;
struct  list_head cfs_tasks;
struct  sched_avg avg_rt;
struct  sched_avg avg_dl;
u64 idle_stamp;
u64 avg_idle;
unsigned long wake_stamp;
u64 wake_avg_idle;
u64 max_idle_balance_cost;
struct  rcuwait hotplug_wait;
u64 prev_steal_time;
unsigned long calc_load_update;
long calc_load_active;
call_single_data_t hrtick_csd;
struct  hrtimer hrtick_timer;
ktime_t hrtick_time;
struct  sched_info rq_sched_info;
unsigned long long rq_cpu_time;
unsigned int yld_count;
unsigned int sched_count;
unsigned int sched_goidle;
unsigned int ttwu_count;
unsigned int ttwu_local;
struct  cpuidle_state *idle_state;
unsigned int nr_pinned;
unsigned int push_busy;
struct  cpu_stop_work push_work;
cpumask_var_t scratch_mask;};
struct  bin_attribute{
struct  attribute attr;
size_t size;
void *private;
struct  address_space* (*f_mapping)() ;
ssize_t (*read)(struct  file*,struct  kobject*,struct  bin_attribute*,char*,loff_t,size_t) ;
ssize_t (*write)(struct  file*,struct  kobject*,struct  bin_attribute*,char*,loff_t,size_t) ;
int (*mmap)(struct  file*,struct  kobject*,struct  bin_attribute*,struct  vm_area_struct*) ;};
struct  sysfs_ops{
ssize_t (*show)(struct  kobject*,struct  attribute*,char*) ;
ssize_t (*store)(struct  kobject*,struct  attribute*,char*,size_t) ;};
struct  perf_branch_stack{
__u64 nr;
__u64 hw_idx;
struct  perf_branch_entry entries[];};
struct  perf_sample_data{
u64 sample_flags;
u64 period;
u64 dyn_size;
u64 type;
struct  {
u32 pid;
u32 tid;} tid_entry;
u64 time;
u64 id;
struct  {
u32 cpu;
u32 reserved;} cpu_entry;
u64 ip;
struct  perf_callchain_entry *callchain;
struct  perf_raw_record *raw;
struct  perf_branch_stack *br_stack;
union  perf_sample_weight weight;
union  perf_mem_data_src data_src;
u64 txn;
struct  perf_regs regs_user;
struct  perf_regs regs_intr;
u64 stack_user_size;
u64 stream_id;
u64 cgroup;
u64 addr;
u64 phys_addr;
u64 data_page_size;
u64 code_page_size;
u64 aux_size;};
struct  super_block{
struct  list_head s_list;
dev_t s_dev;
unsigned char s_blocksize_bits;
unsigned long s_blocksize;
loff_t s_maxbytes;
struct  file_system_type *s_type;
struct  super_operations *s_op;
struct  dquot_operations *dq_op;
struct  quotactl_ops *s_qcop;
struct  export_operations *s_export_op;
unsigned long s_flags;
unsigned long s_iflags;
unsigned long s_magic;
struct  dentry *s_root;
struct  rw_semaphore s_umount;
int s_count;
atomic_t s_active;
void *s_security;
struct  xattr_handler **s_xattr;
struct  hlist_bl_head s_roots;
struct  list_head s_mounts;
struct  block_device *s_bdev;
struct  backing_dev_info *s_bdi;
struct  mtd_info *s_mtd;
struct  hlist_node s_instances;
unsigned int s_quota_types;
struct  quota_info s_dquot;
struct  sb_writers s_writers;
void *s_fs_info;
u32 s_time_gran;
time64_t s_time_min;
time64_t s_time_max;
__u32 s_fsnotify_mask;
struct  fsnotify_mark_connector *s_fsnotify_marks;
char s_id[6];
uuid_t s_uuid;
unsigned int s_max_links;
struct  mutex s_vfs_rename_mutex;
char *s_subtype;
struct  dentry_operations *s_d_op;
struct  shrinker s_shrink;
atomic_long_t s_remove_count;
atomic_long_t s_fsnotify_connectors;
int s_readonly_remount;
errseq_t s_wb_err;
struct  workqueue_struct *s_dio_done_wq;
struct  hlist_head s_pins;
struct  user_namespace *s_user_ns;
struct  list_lru s_dentry_lru;
struct  list_lru s_inode_lru;
struct  callback_head rcu;
struct  work_struct destroy_work;
struct  mutex s_sync_lock;
int s_stack_depth;
spinlock_t s_inode_list_lock;
struct  list_head s_inodes;
spinlock_t s_inode_wblist_lock;
struct  list_head s_inodes_wb;};
struct  psi_group{
};
struct  delayed_call{
void (*fn)(void*) ;
void *arg;};
struct  affinity_context{
struct  cpumask *new_mask;
struct  cpumask *user_mask;
unsigned int flags;};
struct  offset_ctx{
struct  xarray xa;
u32 next_offset;};
struct  mm_struct{
struct  {
struct  {
atomic_t mm_count;} ;
struct  maple_tree mm_mt;
unsigned long (*get_unmapped_area)(struct  file*,unsigned long,unsigned long,unsigned long,unsigned long) ;
unsigned long mmap_base;
unsigned long mmap_legacy_base;
unsigned long mmap_compat_base;
unsigned long mmap_compat_legacy_base;
unsigned long task_size;
pgd_t *pgd;
atomic_t membarrier_state;
atomic_t mm_users;
struct  mm_cid *pcpu_cid;
unsigned long mm_cid_next_scan;
atomic_long_t pgtables_bytes;
int map_count;
spinlock_t page_table_lock;
struct  rw_semaphore mmap_lock;
struct  list_head mmlist;
int mm_lock_seq;
unsigned long hiwater_rss;
unsigned long hiwater_vm;
unsigned long total_vm;
unsigned long locked_vm;
atomic64_t pinned_vm;
unsigned long data_vm;
unsigned long exec_vm;
unsigned long stack_vm;
unsigned long def_flags;
seqcount_t write_protect_seq;
spinlock_t arg_lock;
unsigned long start_code;
unsigned long end_code;
unsigned long start_data;
unsigned long end_data;
unsigned long start_brk;
unsigned long brk;
unsigned long start_stack;
unsigned long arg_start;
unsigned long arg_end;
unsigned long env_start;
unsigned long env_end;
unsigned long saved_auxv[1];
struct  percpu_counter rss_stat[4];
struct  linux_binfmt *binfmt;
mm_context_t context;
unsigned long flags;
spinlock_t ioctx_lock;
struct  kioctx_table *ioctx_table;
struct  user_namespace *user_ns;
struct  file *exe_file;
struct  mmu_notifier_subscriptions *notifier_subscriptions;
atomic_t tlb_flush_pending;
atomic_t tlb_flush_batched;
struct  uprobes_state uprobes_state;
atomic_long_t hugetlb_usage;
struct  work_struct async_put_work;} ;
unsigned long cpu_bitmap[1];};
struct  dentry_operations{
int (*d_revalidate)(struct  dentry*,unsigned int) ;
int (*d_weak_revalidate)(struct  dentry*,unsigned int) ;
int (*d_hash)(struct  dentry*,struct  qstr*) ;
int (*d_compare)(struct  dentry*,unsigned int,char*,struct  qstr*) ;
int (*d_delete)(struct  dentry*) ;
int (*d_init)(struct  dentry*) ;
void (*d_release)(struct  dentry*) ;
void (*d_prune)(struct  dentry*) ;
void (*d_iput)(struct  dentry*,struct  inode*) ;
char* (*d_dname)(struct  dentry*,char*,int) ;
struct  vfsmount* (*d_automount)(struct  path*) ;
int (*d_manage)(struct  path*,bool) ;
struct  dentry* (*d_real)(struct  dentry*,struct  inode*) ;};
struct  rq_flags{
unsigned long flags;
struct  pin_cookie cookie;};
struct  cgroup_namespace{
struct  ns_common ns;
struct  user_namespace *user_ns;
struct  ucounts *ucounts;
struct  css_set *root_cset;};
struct  hrtimer_cpu_base{
raw_spinlock_t lock;
unsigned int cpu;
unsigned int active_bases;
unsigned int clock_was_set_seq;
unsigned int hres_active:1;
unsigned int in_hrtirq:1;
unsigned int hang_detected:1;
unsigned int softirq_activated:1;
unsigned int nr_events;
unsigned short nr_retries;
unsigned short nr_hangs;
unsigned int max_hang_time;
ktime_t expires_next;
struct  hrtimer *next_timer;
ktime_t softirq_expires_next;
struct  hrtimer *softirq_next_timer;
struct  hrtimer_clock_base clock_base[8];};
struct  core_state{
atomic_t nr_threads;
struct  core_thread dumper;
struct  completion startup;};
struct  mempolicy{
atomic_t refcnt;
unsigned short mode;
unsigned short flags;
nodemask_t nodes;
int home_node;
union  {
nodemask_t cpuset_mems_allowed;
nodemask_t user_nodemask;} w;};
struct  ucounts{
struct  hlist_node node;
struct  user_namespace *ns;
kuid_t uid;
atomic_t count;
atomic_long_t ucount[10];
atomic_long_t rlimit[10];};
struct  vm_operations_struct{
void (*open)(struct  vm_area_struct*) ;
void (*close)(struct  vm_area_struct*) ;
int (*may_split)(struct  vm_area_struct*,unsigned long) ;
int (*mremap)(struct  vm_area_struct*) ;
int (*mprotect)(struct  vm_area_struct*,unsigned long,unsigned long,unsigned long) ;
vm_fault_t (*fault)(struct  vm_fault*) ;
vm_fault_t (*huge_fault)(struct  vm_fault*,unsigned int) ;
vm_fault_t (*map_pages)(struct  vm_fault*,unsigned long,unsigned long) ;
unsigned long (*pagesize)(struct  vm_area_struct*) ;
vm_fault_t (*page_mkwrite)(struct  vm_fault*) ;
vm_fault_t (*pfn_mkwrite)(struct  vm_fault*) ;
int (*access)(struct  vm_area_struct*,unsigned long,void*,int,int) ;
char* (*name)(struct  vm_area_struct*) ;
int (*set_policy)(struct  vm_area_struct*,struct  mempolicy*) ;
struct  mempolicy* (*get_policy)(struct  vm_area_struct*,unsigned long) ;
struct  page* (*find_special_page)(struct  vm_area_struct*,unsigned long) ;};
struct  attribute_group{
char *name;
umode_t (*is_visible)(struct  kobject*,struct  attribute*,int) ;
umode_t (*is_bin_visible)(struct  kobject*,struct  bin_attribute*,int) ;
struct  attribute **attrs;
struct  bin_attribute **bin_attrs;};
struct  vma_lock{
struct  rw_semaphore lock;};
struct  seq_operations{
void* (*start)(struct  seq_file*,loff_t*) ;
void (*stop)(struct  seq_file*,void*) ;
void* (*next)(struct  seq_file*,void*,loff_t*) ;
int (*show)(struct  seq_file*,void*) ;};
struct  static_call_site{
s32 addr;
s32 key;};
struct  device_dma_parameters{
unsigned int max_segment_size;
unsigned int min_align_mask;
unsigned long segment_boundary_mask;};
struct  ctl_table{
char *procname;
void *data;
int maxlen;
umode_t mode;
enum {SYSCTL_TABLE_TYPE_DEFAULT,SYSCTL_TABLE_TYPE_PERMANENTLY_EMPTY} type;
proc_handler  proc_handler;
struct  ctl_table_poll *poll;
void *extra1;
void *extra2;};
struct  cgroup_root{
struct  kernfs_root *kf_root;
unsigned int subsys_mask;
int hierarchy_id;
struct  cgroup cgrp;
struct  cgroup *cgrp_ancestor_storage;
atomic_t nr_cgrps;
struct  list_head root_list;
unsigned int flags;
char release_agent_path[6];
char name[6];};
struct  kernfs_ops{
int (*open)(struct  kernfs_open_file*) ;
void (*release)(struct  kernfs_open_file*) ;
int (*seq_show)(struct  seq_file*,void*) ;
void* (*seq_start)(struct  seq_file*,loff_t*) ;
void* (*seq_next)(struct  seq_file*,void*,loff_t*) ;
void (*seq_stop)(struct  seq_file*,void*) ;
ssize_t (*read)(struct  kernfs_open_file*,char*,size_t,loff_t) ;
size_t atomic_write_len;
bool prealloc;
ssize_t (*write)(struct  kernfs_open_file*,char*,size_t,loff_t) ;
__poll_t (*poll)(struct  kernfs_open_file*,struct  poll_table_struct*) ;
int (*mmap)(struct  kernfs_open_file*,struct  vm_area_struct*) ;};
struct  jump_entry{
s32 code;
s32 target;
long key;};
struct  iattr{
unsigned int ia_valid;
umode_t ia_mode;
union  {
kuid_t ia_uid;
vfsuid_t ia_vfsuid;} ;
union  {
kgid_t ia_gid;
vfsgid_t ia_vfsgid;} ;
loff_t ia_size;
struct  timespec64 ia_atime;
struct  timespec64 ia_mtime;
struct  timespec64 ia_ctime;
struct  file *ia_file;};
struct  property{
char *name;
int length;
void *value;
struct  property *next;};
struct  dev_pagemap{
struct  vmem_altmap altmap;
struct  percpu_ref ref;
struct  completion done;
enum memory_type type;
unsigned int flags;
unsigned long vmemmap_shift;
struct  dev_pagemap_ops *ops;
void *owner;
int nr_range;
union  {
struct  range range;
struct  {
struct  {
} __empty_ranges;
struct  range ranges[];} ;} ;};
struct  ctl_node{
struct  rb_node node;
struct  ctl_table_header *header;};
struct  percpu_ref_data{
atomic_long_t count;
percpu_ref_func_t  release;
percpu_ref_func_t  confirm_switch;
bool force_atomic:1;
bool allow_reinit:1;
struct  callback_head rcu;
struct  percpu_ref *ref;};
struct  dev_pm_domain{
struct  dev_pm_ops ops;
int (*start)(struct  device*) ;
void (*detach)(struct  device*,bool) ;
int (*activate)(struct  device*) ;
void (*sync)(struct  device*) ;
void (*dismiss)(struct  device*) ;};
struct  pmu{
struct  list_head entry;
struct  module *module;
struct  device *dev;
struct  device *parent;
struct  attribute_group **attr_groups;
struct  attribute_group **attr_update;
char *name;
int type;
int capabilities;
int *pmu_disable_count;
struct  perf_cpu_pmu_context *cpu_pmu_context;
atomic_t exclusive_cnt;
int task_ctx_nr;
int hrtimer_interval_ms;
unsigned int nr_addr_filters;
void (*pmu_enable)(struct  pmu*) ;
void (*pmu_disable)(struct  pmu*) ;
int (*event_init)(struct  perf_event*) ;
void (*event_mapped)(struct  perf_event*,struct  mm_struct*) ;
void (*event_unmapped)(struct  perf_event*,struct  mm_struct*) ;
int (*add)(struct  perf_event*,int) ;
void (*del)(struct  perf_event*,int) ;
void (*start)(struct  perf_event*,int) ;
void (*stop)(struct  perf_event*,int) ;
void (*read)(struct  perf_event*) ;
void (*start_txn)(struct  pmu*,unsigned int) ;
int (*commit_txn)(struct  pmu*) ;
void (*cancel_txn)(struct  pmu*) ;
int (*event_idx)(struct  perf_event*) ;
void (*sched_task)(struct  perf_event_pmu_context*,bool) ;
struct  kmem_cache *task_ctx_cache;
void (*swap_task_ctx)(struct  perf_event_pmu_context*,struct  perf_event_pmu_context*) ;
void* (*setup_aux)(struct  perf_event*,void**,int,bool) ;
void (*free_aux)(void*) ;
long (*snapshot_aux)(struct  perf_event*,struct  perf_output_handle*,unsigned long) ;
int (*addr_filters_validate)(struct  list_head*) ;
void (*addr_filters_sync)(struct  perf_event*) ;
int (*aux_output_match)(struct  perf_event*) ;
bool (*filter)(struct  pmu*,int) ;
int (*check_period)(struct  perf_event*,u64) ;};
struct  task_group{
struct  cgroup_subsys_state css;
struct  sched_entity **se;
struct  cfs_rq **cfs_rq;
unsigned long shares;
int idle;
atomic_long_t load_avg;
struct  callback_head rcu;
struct  list_head list;
struct  task_group *parent;
struct  list_head siblings;
struct  list_head children;
struct  cfs_bandwidth cfs_bandwidth;};
struct  em_perf_state{
unsigned long frequency;
unsigned long power;
unsigned long cost;
unsigned long flags;};
struct  inode_operations{
struct  dentry* (*lookup)(struct  inode*,struct  dentry*,unsigned int) ;
char* (*get_link)(struct  dentry*,struct  inode*,struct  delayed_call*) ;
int (*permission)(struct  mnt_idmap*,struct  inode*,int) ;
struct  posix_acl* (*get_inode_acl)(struct  inode*,int,bool) ;
int (*readlink)(struct  dentry*,char*,int) ;
int (*create)(struct  mnt_idmap*,struct  inode*,struct  dentry*,umode_t,bool) ;
int (*link)(struct  dentry*,struct  inode*,struct  dentry*) ;
int (*unlink)(struct  inode*,struct  dentry*) ;
int (*symlink)(struct  mnt_idmap*,struct  inode*,struct  dentry*,char*) ;
int (*mkdir)(struct  mnt_idmap*,struct  inode*,struct  dentry*,umode_t) ;
int (*rmdir)(struct  inode*,struct  dentry*) ;
int (*mknod)(struct  mnt_idmap*,struct  inode*,struct  dentry*,umode_t,dev_t) ;
int (*rename)(struct  mnt_idmap*,struct  inode*,struct  dentry*,struct  inode*,struct  dentry*,unsigned int) ;
int (*setattr)(struct  mnt_idmap*,struct  dentry*,struct  iattr*) ;
int (*getattr)(struct  mnt_idmap*,struct  path*,struct  kstat*,u32,unsigned int) ;
ssize_t (*listxattr)(struct  dentry*,char*,size_t) ;
int (*fiemap)(struct  inode*,struct  fiemap_extent_info*,u64,u64) ;
int (*update_time)(struct  inode*,int) ;
int (*atomic_open)(struct  inode*,struct  dentry*,struct  file*,unsigned int,umode_t) ;
int (*tmpfile)(struct  mnt_idmap*,struct  inode*,struct  file*,umode_t) ;
struct  posix_acl* (*get_acl)(struct  mnt_idmap*,struct  dentry*,int) ;
int (*set_acl)(struct  mnt_idmap*,struct  dentry*,struct  posix_acl*,int) ;
int (*fileattr_set)(struct  mnt_idmap*,struct  dentry*,struct  fileattr*) ;
int (*fileattr_get)(struct  dentry*,struct  fileattr*) ;
struct  offset_ctx* (*get_offset_ctx)(struct  inode*) ;};
struct  wakeup_source{
char *name;
int id;
struct  list_head entry;
spinlock_t lock;
struct  wake_irq *wakeirq;
struct  timer_list timer;
unsigned long timer_expires;
ktime_t total_time;
ktime_t max_time;
ktime_t last_time;
ktime_t start_prevent_time;
ktime_t prevent_sleep_time;
unsigned long event_count;
unsigned long active_count;
unsigned long relax_count;
unsigned long expire_count;
unsigned long wakeup_count;
struct  device *dev;
bool active:1;
bool autosleep_enabled:1;};
struct  qc_state{
unsigned int s_incoredqs;
struct  qc_type_state s_state[3];};
struct  srcu_usage{
struct  srcu_node *node;
struct  srcu_node *level[3];
int srcu_size_state;
struct  mutex srcu_cb_mutex;
spinlock_t lock;
struct  mutex srcu_gp_mutex;
unsigned long srcu_gp_seq;
unsigned long srcu_gp_seq_needed;
unsigned long srcu_gp_seq_needed_exp;
unsigned long srcu_gp_start;
unsigned long srcu_last_gp_end;
unsigned long srcu_size_jiffies;
unsigned long srcu_n_lock_retries;
unsigned long srcu_n_exp_nodelay;
bool sda_is_static;
unsigned long srcu_barrier_seq;
struct  mutex srcu_barrier_mutex;
struct  completion srcu_barrier_completion;
atomic_t srcu_barrier_cpu_cnt;
unsigned long reschedule_jiffies;
unsigned long reschedule_count;
struct  delayed_work work;
struct  srcu_struct *srcu_ssp;};
struct  energy_env{
unsigned long task_busy_time;
unsigned long pd_busy_time;
unsigned long cpu_cap;
unsigned long pd_cap;};
struct  cred{
atomic_t usage;
kuid_t uid;
kgid_t gid;
kuid_t suid;
kgid_t sgid;
kuid_t euid;
kgid_t egid;
kuid_t fsuid;
kgid_t fsgid;
unsigned int securebits;
kernel_cap_t cap_inheritable;
kernel_cap_t cap_permitted;
kernel_cap_t cap_effective;
kernel_cap_t cap_bset;
kernel_cap_t cap_ambient;
unsigned char jit_keyring;
struct  key *session_keyring;
struct  key *process_keyring;
struct  key *thread_keyring;
struct  key *request_key_auth;
void *security;
struct  user_struct *user;
struct  user_namespace *user_ns;
struct  ucounts *ucounts;
struct  group_info *group_info;
union  {
int non_rcu;
struct  callback_head rcu;} ;};
struct  srcu_struct{
unsigned int srcu_idx;
struct  srcu_data *sda;
struct  lockdep_map dep_map;
struct  srcu_usage *srcu_sup;};
struct  device_node{
char *name;
phandle phandle;
char *full_name;
struct  fwnode_handle fwnode;
struct  property *properties;
struct  property *deadprops;
struct  device_node *parent;
struct  device_node *child;
struct  device_node *sibling;
unsigned long _flags;
void *data;};
struct  qc_info{
int i_fieldmask;
unsigned int i_flags;
unsigned int i_spc_timelimit;
unsigned int i_ino_timelimit;
unsigned int i_rt_spc_timelimit;
unsigned int i_spc_warnlimit;
unsigned int i_ino_warnlimit;
unsigned int i_rt_spc_warnlimit;};
struct  trace_eval_map{
char *system;
char *eval_string;
unsigned long eval_value;};
struct  io_context{
atomic_long_t refcount;
atomic_t active_ref;
unsigned short ioprio;};
struct  perf_callchain_entry{
__u64 nr;
__u64 ip[];};

extern struct cpumask __cpu_online_mask;

DECLARE_PER_CPU(struct sched_domain __rcu *, sd_asym_cpucapacity);

DECLARE_PER_CPU_READ_MOSTLY(unsigned long, this_cpu_off);

static DEFINE_PER_CPU(cpumask_var_t, select_rq_mask);

extern unsigned long __per_cpu_offset[NR_CPUS];

DECLARE_PER_CPU_SHARED_ALIGNED(struct rq, runqueues);

void rcu_read_unlock();

int util_fits_cpu(unsigned long util, unsigned long uclamp_min, unsigned long uclamp_max, int cpu);

unsigned long uclamp_rq_get(struct rq * rq, enum uclamp_id clamp_id);

bool uclamp_rq_is_idle(struct rq * rq);

unsigned long uclamp_task_util(struct task_struct * p, unsigned long uclamp_min, unsigned long uclamp_max);

void sync_entity_load_avg(struct sched_entity * se);

struct cpumask * sched_domain_span(struct sched_domain * sd);

int rcu_read_lock_held();

void rcu_read_lock();

unsigned long uclamp_eff_value(struct task_struct * p, enum uclamp_id clamp_id);

bool uclamp_is_used();

void eenv_task_busy_time(struct energy_env * eenv, struct task_struct * p, int prev_cpu);

unsigned long find_next_bit(const unsigned long * addr, unsigned long size, unsigned long offset);

void eenv_pd_busy_time(struct energy_env * eenv, struct cpumask * pd_cpus, struct task_struct * p);

bool cpumask_test_cpu(int cpu, const struct cpumask * cpumask);

unsigned int cpumask_first(const struct cpumask * srcp);

bool cpumask_empty(const struct cpumask * srcp);

bool cpumask_and(struct cpumask * dstp, const struct cpumask * src1p, const struct cpumask * src2p);

unsigned long cpu_util(int cpu, struct task_struct * p, int dst_cpu, int boost);

unsigned long compute_energy(struct energy_env * eenv, struct perf_domain * pd, struct cpumask * pd_cpus, struct task_struct * p, int dst_cpu);

unsigned long capacity_of(int cpu);

unsigned long arch_scale_thermal_pressure(int cpu);

unsigned long arch_scale_cpu_capacity(int cpu);

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
	pd = rcu_dereference(rd->pd);
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
