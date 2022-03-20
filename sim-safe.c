/*
 * sim-safe.c - sample functional simulator implementation
 *
 * This file is a part of the SimpleScalar tool suite written by
 * Todd M. Austin as a part of the Multiscalar Research Project.
 *  
 * The tool suite is currently maintained by Doug Burger and Todd M. Austin.
 * 
 * Copyright (C) 1994, 1995, 1996, 1997, 1998 by Todd M. Austin
 *
 * This source file is distributed "as is" in the hope that it will be
 * useful.  The tool set comes with no warranty, and no author or
 * distributor accepts any responsibility for the consequences of its
 * use. 
 * 
 * Everyone is granted permission to copy, modify and redistribute
 * this tool set under the following conditions:
 * 
 *    This source code is distributed for non-commercial use only. 
 *    Please contact the maintainer for restrictions applying to 
 *    commercial use.
 *
 *    Permission is granted to anyone to make or distribute copies
 *    of this source code, either as received or modified, in any
 *    medium, provided that all copyright notices, permission and
 *    nonwarranty notices are preserved, and that the distributor
 *    grants the recipient permission for further redistribution as
 *    permitted by this document.
 *
 *    Permission is granted to distribute this file in compiled
 *    or executable form under the same conditions that apply for
 *    source code, provided that either:
 *
 *    A. it is accompanied by the corresponding machine-readable
 *       source code,
 *    B. it is accompanied by a written offer, with no time limit,
 *       to give anyone a machine-readable copy of the corresponding
 *       source code in return for reimbursement of the cost of
 *       distribution.  This written offer must permit verbatim
 *       duplication by anyone, or
 *    C. it is distributed by someone who received only the
 *       executable form, and is accompanied by a copy of the
 *       written offer of source code that they received concurrently.
 *
 * In other words, you are welcome to use, share and improve this
 * source file.  You are forbidden to forbid anyone else to use, share
 * and improve what you give them.
 *
 * INTERNET: dburger@cs.wisc.edu
 * US Mail:  1210 W. Dayton Street, Madison, WI 53706
 *
 * $Id: sim-safe.c,v 1.1.1.1 2000/05/26 15:18:58 taustin Exp $
 *
 * $Log: sim-safe.c,v $
 * Revision 1.1.1.1  2000/05/26 15:18:58  taustin
 * SimpleScalar Tool Set
 *
 *
 * Revision 1.9  1999/12/31 18:53:24  taustin
 * quad_t naming conflicts removed
 *
 * Revision 1.8  1999/12/13 18:47:13  taustin
 * cross endian execution support added
 *
 * Revision 1.7  1998/08/31 17:11:01  taustin
 * added register checksuming support, viewable with "-v" flag
 *
 * Revision 1.6  1998/08/27 16:38:25  taustin
 * implemented host interface description in host.h
 * added target interface support
 * added support for register and memory contexts
 * instruction predecoding moved to loader module
 * Alpha target support added
 * added support for qword's
 * added fault support
 * added option ("-max:inst") to limit number of instructions analyzed
 * added target-dependent myprintf() support
 *
 * Revision 1.5  1997/03/11  17:14:57  taustin
 * updated copyright
 * long/int tweaks made for ALPHA target support
 * supported added for non-GNU C compilers
 *
 * Revision 1.4  1997/01/06  16:06:28  taustin
 * updated comments
 * opt_reg_header() call now prints simulator overview message
 * access variable now generalized to is_write boolean flag
 *
 * Revision 1.3  1996/12/27  15:54:04  taustin
 * updated comments
 * integrated support for options and stats packages
 * added sim_init() code
 *
 * Revision 1.1  1996/12/05  18:52:32  taustin
 * Initial revision
 *
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <limits.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"
#define DNA -1

#define NINIT_INST 100
#define NUM_BINS 21

typedef struct {
  counter_t *arr;
  size_t used;
  size_t max_sz;
} cntr_arr;

typedef struct {
  //all cntr_arr are per register per inst
  cntr_arr reg_raw; //number of reads after write 
  cntr_arr reg_lifetime; //number of instructions b/w write and last read
  cntr_arr reg_wr_dist; //distance in instructions b/w writes to the same register
  counter_t reg_wr_to; //number of instructions since last write to register, if 0 reg has not been written to

} inst_reg_cntr;

static counter_t reg_ready[MD_TOTAL_REGS];
static counter_t sim_num_lduh = 0;

//part 2
//stores number of cycles since last write, if not written to is 0, reset to 1 on a new write
static counter_t reg_wr_to[MD_TOTAL_REGS];
//stores number of reads after a write, resets to 0 if a new write occurs
static counter_t reg_raw[MD_TOTAL_REGS];
//stores maximum number of raw cyles for a register 
static counter_t reg_raw_max[MD_TOTAL_REGS];

static counter_t reg_raw_cnt_tmp[MD_TOTAL_REGS];
static counter_t reg_raw_sum_tmp[MD_TOTAL_REGS];

static int cum_bin_map [] = {
  0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
  32,64,128,256
};

typedef struct {
    counter_t hist_bins[NUM_BINS];
    counter_t cur;
    counter_t min;
    counter_t max;
    counter_t sum;
    counter_t avg;
} reg_stats;

typedef struct {
    reg_stats reg_raw;
    reg_stats reg_lifetime;
    reg_stats reg_wr_dist;
    reg_stats reg_wr_to;
    counter_t wr_count;
} reg_total_info;

static reg_total_info reg_info_arr[MD_TOTAL_REGS];

static counter_t global_max;
static counter_t global_min;
static counter_t global_avg;
static counter_t global_wr_cnt;
static counter_t global_sum;
static counter_t global_hist[NUM_BINS];

// static inst_reg_cntr reg_info_arr[MD_TOTAL_REGS];

//dynamic counter_t array functions
void init_arr(cntr_arr *a, int init_sz)
{
  a->arr = malloc(init_sz * sizeof(counter_t));
  a->used = 0;
  a->max_sz = init_sz;
}

void ins_arr(cntr_arr *a, counter_t ele)
{
  if(a->used == a->max_sz)
  {
    //double arr size if its equal to the max
    a->max_sz *= 2;
    a->arr = realloc(a->arr, a->max_sz * sizeof(counter_t));
  }
  a->arr[a->used++] = ele;
}

void free_arr(cntr_arr *a)
{
  free(a->arr);
  a->arr = NULL;
  a->used = a->max_sz = 0;
}

void free_inst_reg_ctnr_arr(inst_reg_cntr *iregs)
{
  int i;
  for(i=0;i<MD_TOTAL_REGS;i++)
  {
    free_arr(&iregs[i].reg_raw);
    free_arr(&iregs[i].reg_lifetime);
    free_arr(&iregs[i].reg_wr_dist);
  }
}
/*
 * This file implements a functional simulator.  This functional simulator is
 * the simplest, most user-friendly simulator in the simplescalar tool set.
 * Unlike sim-fast, this functional simulator checks for all instruction
 * errors, and the implementation is crafted for clarity rather than speed.
 */

/* simulated registers */
static struct regs_t regs;

/* simulated memory */
static struct mem_t *mem = NULL;

/* track number of refs */
static counter_t sim_num_refs = 0;

/* maximum number of inst's to execute */
static unsigned int max_insts;

/* register simulator-specific options */
void
sim_reg_options(struct opt_odb_t *odb)
{
  opt_reg_header(odb, 
"sim-safe: This simulator implements a functional simulator.  This\n"
"functional simulator is the simplest, most user-friendly simulator in the\n"
"simplescalar tool set.  Unlike sim-fast, this functional simulator checks\n"
"for all instruction errors, and the implementation is crafted for clarity\n"
"rather than speed.\n"
		 );

  /* instruction limit */
  opt_reg_uint(odb, "-max:inst", "maximum number of inst's to execute",
	       &max_insts, /* default */0,
	       /* print */TRUE, /* format */NULL);

}

/* check simulator-specific option values */
void
sim_check_options(struct opt_odb_t *odb, int argc, char **argv)
{
  /* nada */
}

/* register simulator-specific statistics */
void
sim_reg_stats(struct stat_sdb_t *sdb)
{
  #define reg_cntr_str_sz 50
  int i,j;
  //stores string of register index
  char reg_raw_max_str[reg_cntr_str_sz];
  char reg_raw_min_str[reg_cntr_str_sz];
  char reg_raw_avg_str[reg_cntr_str_sz];
  char reg_raw_cnt_str[reg_cntr_str_sz];
  char reg_raw_sum_str[reg_cntr_str_sz];

  char reg_wr_lifetime_str[reg_cntr_str_sz];

  for(i=0;i<MD_TOTAL_REGS;i++)
  {
    reg_raw_cnt_tmp[i] = reg_info_arr[i].wr_count;
    reg_raw_sum_tmp[i] = reg_info_arr[i].reg_raw.sum;
    sprintf(reg_raw_max_str,"reg_%d_raw_max",i);//,reg_info_arr[i].reg_raw.max);
    sprintf(reg_raw_min_str,"END HISTOGRAM\nreg_%d_raw_min\t\t",i);//,reg_info_arr[i].reg_raw.min);
    sprintf(reg_raw_avg_str,"reg_%d_raw_avg",i);//,reg_info_arr[i].reg_raw.avg);
    sprintf(reg_raw_cnt_str,"reg_%d_raw_cnt",i);//,reg_info_arr[i].reg_raw.avg);
    sprintf(reg_raw_sum_str,"reg_%d_raw_sum",i);//,reg_info_arr[i].reg_raw.avg);
    stat_reg_counter(sdb,reg_raw_min_str,"min number of read after writes for reg",
    &reg_info_arr[i].reg_raw.min,reg_info_arr[i].reg_raw.min,NULL);
    // stat_reg_counter(sdb,reg_raw_max_str,"max number of read after writes for reg",
    // &reg_info_arr[i].reg_raw.max,reg_info_arr[i].reg_raw.max,NULL);
    stat_reg_counter(sdb,reg_raw_max_str,"max number of read after writes for reg",
    &reg_info_arr[i].reg_raw.max,reg_info_arr[i].reg_raw.max,NULL);

    // stat_reg_counter(sdb,reg_raw_cnt_str,"cnt number of read after writes for reg",
    // &reg_info_arr[i].wr_count,reg_info_arr[i].wr_count,NULL);
    // stat_reg_counter(sdb,reg_raw_sum_str,"sum number of read after writes for reg",
    // &reg_info_arr[i].reg_raw.sum,reg_info_arr[i].reg_raw.sum,NULL);
    stat_reg_counter(sdb,reg_raw_avg_str,"avg number of read after writes for reg",
    &reg_info_arr[i].reg_raw.avg,reg_info_arr[i].reg_raw.avg,NULL);
    for(j=0;j<NUM_BINS;j++)
    {
      char reg_raw_hist_str[reg_cntr_str_sz];
      if(j == 0)
      {
        sprintf(reg_raw_hist_str,"START HISTOGRAM FOR REG %d\nreg_%d_raw_bin_%d",i,i,cum_bin_map[j]);//,reg_info_arr[i].reg_raw.max);
      }
      else if(j == NUM_BINS-1)
      {
        sprintf(reg_raw_hist_str,"reg_%d_raw_bin_%d",i,cum_bin_map[j]);//,reg_info_arr[i].reg_raw.max);
      }
      else
        sprintf(reg_raw_hist_str,"reg_%d_raw_bin_%d",i,cum_bin_map[j]);//,reg_info_arr[i].reg_raw.max);
      stat_reg_counter(sdb,reg_raw_hist_str,"cumulative distribution for number of read after writes for reg",
      &reg_info_arr[i].reg_raw.hist_bins[j],reg_info_arr[i].reg_raw.hist_bins[j],NULL);
    }
    // stat_reg_counter(sdb,reg_raw_max_str,"min number of read after writes for reg",
    // &reg_info_arr[i].reg_raw.max,reg_info_arr[i].reg_raw.cnt,NULL);

    // stat_reg_formula(sdb,reg_raw_avg_str,
    //   "avg number of read after writes for reg", "reg_raw_sum_tmp[i] / reg_raw_cnt_tmp[i]", NULL);

    // fprintf(stderr,reg_raw_max_str);
    // fprintf(stderr,reg_raw_min_str);
    // fprintf(stderr,reg_raw_avg_str);
    // for(j=0;j<NUM_BINS;j++)
    // {
      
    // }
    // sprintf()
    // sprintf(reg_raw_min_str,"reg_%d_raw_min",i);
    // sprintf(reg_raw_avg_str,"reg_%d_raw_min",i);
    // sprintf(reg_wr_lifetime_str,"reg_%d_wr_lifetime_str",i);
    // stat_reg_counter(sdb,reg_raw_max_str,"old max number of read after writes for reg",
    // &reg_raw_max[i],reg_raw_max[i],NULL);
    // fprintf(stderr,"");
    // stat_reg_counter(sdb,reg_raw_min_str,"min number of read after writes for reg",
    // &reg_info_arr[i].reg_raw.min,reg_info_arr[i].reg_raw.min,NULL);
    // stat_reg_formula(sdb, reg_raw_avg_str,
    // "average number of read after writes for reg",
    // "reg_info_arr[i].reg_raw.sum / reg_info_arr[i].wr_count", NULL);
    // stat_reg_counter(sdb,reg_raw_avg_str," number of read after writes for reg",
    // &reg_info_arr[i].reg_raw.avg,reg_info_arr[i].reg_raw.avg,NULL);
  }
  stat_reg_counter(sdb,"global_raw_max",
       "global max number of raws",
       &global_max, global_max, NULL);
  stat_reg_counter(sdb,"global_raw_min",
       "global max number of raws",
       &global_min, global_min, NULL);
  stat_reg_counter(sdb,"global_raw_avg",
      "global avg number of raws",
      &global_avg, global_avg, NULL);
  stat_reg_counter(sdb,"sim_num_lduh",
       "total number of load use hazards",
       &sim_num_lduh, sim_num_lduh, NULL);
  stat_reg_formula(sdb,"sim_load_use_ratio",
        "load use fraction", "sim_num_lduh / sim_num_insn", NULL);
  stat_reg_counter(sdb, "sim_num_insn",
		   "total number of instructions executed",
		   &sim_num_insn, sim_num_insn, NULL);
  stat_reg_counter(sdb, "sim_num_refs",
		   "total number of loads and stores executed",
		   &sim_num_refs, 0, NULL);
  stat_reg_int(sdb, "sim_elapsed_time",
	       "total simulation time in seconds",
	       &sim_elapsed_time, 0, NULL);
  stat_reg_formula(sdb, "sim_inst_rate",
		   "simulation speed (in insts/sec)",
		   "sim_num_insn / sim_elapsed_time", NULL);
  ld_reg_stats(sdb);
  mem_reg_stats(mem, sdb);
}

/* initialize the simulator */
void
sim_init(void)
{
  sim_num_refs = 0;

  /* allocate and initialize register file */
  regs_init(&regs);

  /* allocate and initialize memory space */
  mem = mem_create("mem");
  mem_init(mem);
}

/* load program into simulated state */
void
sim_load_prog(char *fname,		/* program to load */
	      int argc, char **argv,	/* program arguments */
	      char **envp)		/* program environment */
{
  /* load program text and data, set up environment, memory, and regs */
  ld_load_prog(fname, argc, argv, envp, &regs, mem, TRUE);

  /* initialize the DLite debugger */
  dlite_init(md_reg_obj, dlite_mem_obj, dlite_mstate_obj);
}

/* print simulator-specific configuration information */
void
sim_aux_config(FILE *stream)		/* output stream */
{
  /* nothing currently */
}

/* dump simulator-specific auxiliary simulator statistics */
void
sim_aux_stats(FILE *stream)		/* output stream */
{
  /* nada */
}

/* un-initialize simulator-specific state */
void
sim_uninit(void)
{
  /* nada */
}


/*
 * configure the execution engine
 */

/*
 * precise architected register accessors
 */

/* next program counter */
#define SET_NPC(EXPR)		(regs.regs_NPC = (EXPR))

/* current program counter */
#define CPC			(regs.regs_PC)

/* general purpose registers */
#define GPR(N)			(regs.regs_R[N])
#define SET_GPR(N,EXPR)		(regs.regs_R[N] = (EXPR))

#if defined(TARGET_PISA)

/* floating point registers, L->word, F->single-prec, D->double-prec */
#define FPR_L(N)		(regs.regs_F.l[(N)])
#define SET_FPR_L(N,EXPR)	(regs.regs_F.l[(N)] = (EXPR))
#define FPR_F(N)		(regs.regs_F.f[(N)])
#define SET_FPR_F(N,EXPR)	(regs.regs_F.f[(N)] = (EXPR))
#define FPR_D(N)		(regs.regs_F.d[(N) >> 1])
#define SET_FPR_D(N,EXPR)	(regs.regs_F.d[(N) >> 1] = (EXPR))

/* miscellaneous register accessors */
#define SET_HI(EXPR)		(regs.regs_C.hi = (EXPR))
#define HI			(regs.regs_C.hi)
#define SET_LO(EXPR)		(regs.regs_C.lo = (EXPR))
#define LO			(regs.regs_C.lo)
#define FCC			(regs.regs_C.fcc)
#define SET_FCC(EXPR)		(regs.regs_C.fcc = (EXPR))

#elif defined(TARGET_ALPHA)

/* floating point registers, L->word, F->single-prec, D->double-prec */
#define FPR_Q(N)		(regs.regs_F.q[N])
#define SET_FPR_Q(N,EXPR)	(regs.regs_F.q[N] = (EXPR))
#define FPR(N)			(regs.regs_F.d[(N)])
#define SET_FPR(N,EXPR)		(regs.regs_F.d[(N)] = (EXPR))

/* miscellaneous register accessors */
#define FPCR			(regs.regs_C.fpcr)
#define SET_FPCR(EXPR)		(regs.regs_C.fpcr = (EXPR))
#define UNIQ			(regs.regs_C.uniq)
#define SET_UNIQ(EXPR)		(regs.regs_C.uniq = (EXPR))

#else
#error No ISA target defined...
#endif

/* precise architected memory state accessor macros */
#define READ_BYTE(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_BYTE(mem, addr = (SRC)))
#define READ_HALF(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_HALF(mem, addr = (SRC)))
#define READ_WORD(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_WORD(mem, addr = (SRC)))
#ifdef HOST_HAS_QWORD
#define READ_QWORD(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_QWORD(mem, addr = (SRC)))
#endif /* HOST_HAS_QWORD */

#define WRITE_BYTE(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_BYTE(mem, addr = (DST), (SRC)))
#define WRITE_HALF(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_HALF(mem, addr = (DST), (SRC)))
#define WRITE_WORD(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_WORD(mem, addr = (DST), (SRC)))
#ifdef HOST_HAS_QWORD
#define WRITE_QWORD(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_QWORD(mem, addr = (DST), (SRC)))
#endif /* HOST_HAS_QWORD */

/* system call handler macro */
#define SYSCALL(INST)	sys_syscall(&regs, mem_access, mem, INST, TRUE)

/* start simulation, program loaded, processor precise state initialized */
void
sim_main(void)
{
  int r_out[2], r_in[3];
  md_inst_t inst;
  register md_addr_t addr;
  enum md_opcode op;
  register int is_write;
  enum md_fault_type fault;

  fprintf(stderr, "sim: ** starting functional simulation **\n");
  //initialize structure to contain all instruction per reg information
  int reg_id;
  for(reg_id=0;reg_id<MD_TOTAL_REGS;reg_id++)
  {
    reg_info_arr[reg_id].reg_raw.min = ULONG_MAX;
    reg_info_arr[reg_id].reg_lifetime.min = ULONG_MAX;
    reg_info_arr[reg_id].reg_wr_dist.min = ULONG_MAX;
    reg_info_arr[reg_id].reg_raw.max = ULONG_MAX;
    reg_info_arr[reg_id].reg_lifetime.max = ULONG_MAX;
    reg_info_arr[reg_id].reg_wr_dist.max = ULONG_MAX;
    reg_info_arr[reg_id].reg_raw.avg = ULONG_MAX;
    reg_info_arr[reg_id].reg_lifetime.avg = ULONG_MAX;
    reg_info_arr[reg_id].reg_wr_dist.avg = ULONG_MAX;
  }
//   for(reg_id=0;reg_id<MD_TOTAL_REGS;reg_id++)
//   {
//     init_arr(&reg_info_arr[reg_id].reg_raw, NINIT_INST);
//     init_arr(&reg_info_arr[reg_id].reg_lifetime, NINIT_INST);
//     init_arr(&reg_info_arr[reg_id].reg_wr_dist, NINIT_INST);
//   }

  /* set up initial default next PC */
  regs.regs_NPC = regs.regs_PC + sizeof(md_inst_t);

  /* check for DLite debugger entry condition */
  if (dlite_check_break(regs.regs_PC, /* !access */0, /* addr */0, 0, 0))
    dlite_main(regs.regs_PC - sizeof(md_inst_t),
	       regs.regs_PC, sim_num_insn, &regs, mem);

  while (TRUE)
    {
      /* maintain $r0 semantics */
      regs.regs_R[MD_REG_ZERO] = 0;
#ifdef TARGET_ALPHA
      regs.regs_F.d[MD_REG_ZERO] = 0.0;
#endif /* TARGET_ALPHA */

      /* get the next instruction to execute */
      MD_FETCH_INST(inst, mem, regs.regs_PC);

      /* keep an instruction count */
      sim_num_insn++;

      /* set default reference address and access mode */
      addr = 0; is_write = FALSE;

      /* set default fault - none */
      fault = md_fault_none;

      /* decode the instruction */
      MD_SET_OPCODE(op, inst);

      /* execute the instruction */
      switch (op)
	    {
#define DEFINST(OP,MSK,NAME,OPFORM,RES,FLAGS,O1,O2,I1,I2,I3)		\
	case OP:							                                        \
          r_out[0] = (O1); r_out[1] = (O2);                     \
          r_in[0] = (I1); r_in[1] = (I2); r_in[2] = (I3);       \
          SYMCAT(OP,_IMPL);						                          \
          break;
#define DEFLINK(OP,MSK,NAME,MASK,SHIFT)					\
        case OP:							\
          panic("attempted to execute a linking opcode");
#define CONNECT(OP)
#define DECLARE_FAULT(FAULT)						\
	  { fault = (FAULT); break; }
#include "machine.def"
	default:
	  panic("attempted to execute a bogus opcode");
      }
      //for each value written into a register, begin tracking the number of instructions which read it afterwards
      //if there is a value being written regardless of instruction
      int i,j,k;
      //loop through all registers
      for(i=0;i<MD_TOTAL_REGS;i++)
      {
        // if(reg_info_arr[i].reg_wr_to > 0)
        // {
        //   reg_info_arr[i].reg_wr_to++;
        //   //incrementing the number of instructions passed since a specific write occurred
        //   //ins_arr(&reg_info_arr[i].reg_lifetime,reg_info_arr[i].reg_lifetime);
        // }
        /*************************************************REG INFO ARR STRUCT*************************************/
        //if the reg has been written to
        if(reg_info_arr[i].reg_wr_to.cur > 0)
        {
          //increment to count cycles since last write
          reg_info_arr[i].reg_wr_to.cur++;
        }

        /*************************************************REG INFO ARR STRUCT*************************************/
        //if the reg has been written to
        if(reg_wr_to[i] > 0)
        {
          //increment to count cycles since last write
          reg_wr_to[i]++;
        }
      }
      //loop through all output regs
      for(j=0;j<2;j++)
      {
        //if write occurred at output register
        if(r_out[j] != DNA )
        {
          /*************************************************REG INFO ARR STRUCT*************************************/
          //set raw stats on a write
          //if the current raw is > the max so far set the max to cur
          if(reg_info_arr[r_out[j]].reg_wr_to.cur > 0)
          {
            //if the current raw is lt the current minimum, set the min to cur
            //or if the min is unset (-1) set the raw to the current value in before the write resets
            if(reg_info_arr[r_out[j]].reg_raw.cur < reg_info_arr[r_out[j]].reg_raw.min || reg_info_arr[r_out[j]].reg_raw.min < 0)
            {
              reg_info_arr[r_out[j]].reg_raw.min = reg_info_arr[r_out[j]].reg_raw.cur;
            }
            //cumulative distribution 
            for(k=0;k<20;k++)
            {
              if(reg_info_arr[r_out[j]].reg_raw.cur >= cum_bin_map[k] && reg_info_arr[r_out[j]].reg_raw.cur < cum_bin_map[k+1])
              {
                reg_info_arr[r_out[j]].reg_raw.hist_bins[k]++;
                break;
              }
            }
            //corner case of >=256
            if(reg_info_arr[r_out[j]].reg_raw.cur >= cum_bin_map[NUM_BINS-1])
            {
              reg_info_arr[r_out[j]].reg_raw.hist_bins[NUM_BINS-1]++;
            }
            //average
            reg_info_arr[r_out[j]].reg_raw.sum += reg_info_arr[r_out[j]].reg_raw.cur;
            reg_info_arr[r_out[j]].wr_count++;
            reg_info_arr[r_out[j]].reg_raw.avg = (counter_t) (reg_info_arr[r_out[j]].reg_raw.sum/reg_info_arr[r_out[j]].wr_count);
            //global variables
            global_sum += reg_info_arr[r_out[j]].reg_raw.cur;
            global_wr_cnt++;
            global_avg = (counter_t) (global_sum/global_wr_cnt);
          }
          //reset raw reg
          reg_info_arr[r_out[j]].reg_raw.cur = 0;
          //set that a reg has been written to
          reg_info_arr[r_out[j]].reg_wr_to.cur = 1;
          
          /*************************************************REG INFO ARR STRUCT*************************************/
          //if number of reads is gt the current max, save into max
          if(reg_raw[r_out[j]] > reg_raw_max[r_out[j]])
            reg_raw_max[r_out[j]] = reg_raw[r_out[j]];
          //reset raw reg
          reg_raw[r_out[j]] = 0;
          //set that a reg has been written to
          reg_wr_to[r_out[j]] = 1;
        }
      }

      //loop through all input regs
      for(j=0;j<3;j++)
      {
        //if a read has just occured and it happens to be after a write to the same register
        if(r_in[j] != DNA && reg_info_arr[r_in[j]].reg_wr_to.cur > 0)
        {
          reg_info_arr[r_in[j]].reg_raw.cur++;
          if(reg_info_arr[r_in[j]].reg_raw.cur > reg_info_arr[r_in[j]].reg_raw.max)
            reg_info_arr[r_in[j]].reg_raw.max = reg_info_arr[r_in[j]].reg_raw.cur;
          if(reg_info_arr[r_in[j]].reg_raw.cur > global_max)
            global_max = reg_info_arr[r_in[j]].reg_raw.cur;
        }
        
        
        // if(r_in[j] != DNA && reg_info_arr[r_in[j]].reg_wr_to > 0)
        // {
        //   reg_info_arr[r_in[j]].reg_raw
        // }
        //read occurred at input register & write has occurred at least once
        if(r_in[j] != DNA && reg_wr_to[r_in[j]] > 0)
        {
          reg_raw[r_in[j]]++;
        }

      }
      //added to track load hazards / load use
      for(i=0;i<3;i++)
      {
        //if the second (read) register IS used (if == DNA then register is unused),
        //and the other registers reg_ready value is gt the number of current instructions executed THEN there is a load hazard
        if(r_in[1] != DNA && reg_ready[r_in[i]] > sim_num_insn)
        {
          sim_num_lduh++;
          break;
        }
      }
      //flags load target regs indicating they ont be available for next inst to see
      if((MD_OP_FLAGS(op) & F_MEM) && (MD_OP_FLAGS(op) & F_LOAD))
      {
        if(r_out[0] != DNA)
          reg_ready[r_out[0]] = sim_num_insn + 2;
        if(r_out[1] != DNA)
          reg_ready[r_out[1]] = sim_num_insn + 2;
      }
      if (fault != md_fault_none)
	fatal("fault (%d) detected @ 0x%08p", fault, regs.regs_PC);

      if (verbose)
	{
	  myfprintf(stderr, "%10n [xor: 0x%08x] @ 0x%08p: ",
		    sim_num_insn, md_xor_regs(&regs), regs.regs_PC);
	  md_print_insn(inst, regs.regs_PC, stderr);
	  if (MD_OP_FLAGS(op) & F_MEM)
	    myfprintf(stderr, "  mem: 0x%08p", addr);
	  fprintf(stderr, "\n");
	  /* fflush(stderr); */
	}

  //F_MEM is a load, F_STORE is a store (makes sense ig)
  if (MD_OP_FLAGS(op) & F_MEM)
	{
	  sim_num_refs++;
	  if (MD_OP_FLAGS(op) & F_STORE)
	    is_write = TRUE;
	}

      /* check for DLite debugger entry condition */
      if (dlite_check_break(regs.regs_NPC,
			    is_write ? ACCESS_WRITE : ACCESS_READ,
			    addr, sim_num_insn, sim_num_insn))
	dlite_main(regs.regs_PC, regs.regs_NPC, sim_num_insn, &regs, mem);

      /* go to the next instruction */
      regs.regs_PC = regs.regs_NPC;
      regs.regs_NPC += sizeof(md_inst_t);

      /* finish early? */
      if (max_insts && sim_num_insn >= max_insts)
      {
        // free_inst_reg_ctnr_arr(reg_info_arr);
        return;
      }
    }
    // free_inst_reg_ctnr_arr(reg_info_arr);
}
