/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * rp_propagator.h                                                          *
 ****************************************************************************/

#ifndef RP_PROPAGATOR_H
#define RP_PROPAGATOR_H 1

#include "rp_config.h"
#include "rp_memory.h"
#include "rp_container.h"
#include "rp_operator.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ------------------------------------------------- */
/* Dependency function: Variable -> Set of operators */
/* ------------------------------------------------- */

typedef struct
{
  int size;         /* number of variables                    */
  rp_vector * op;   /* vector of operators for every variable */
}
rp_dependency_def;

typedef rp_dependency_def rp_dependency[1];

#define rp_dependency_size(d)   (d)[0].size
#define rp_dependency_ptr(d)    (d)[0].op
#define rp_dependency_elem(d,i) (d)[0].op[i]

/* Creation of an empty dependency function */
void rp_dependency_create  (rp_dependency * d);

/* Destruction of a dependency function */
void rp_dependency_destroy (rp_dependency * d);

/* Insertion of o in the dependency of v in d */
int  rp_dependency_insert  (rp_dependency d, rp_operator * o, int v);

/* ------------------------------------------------------ */
/* Priority queue of operators for constraint propagation */
/* ------------------------------------------------------ */

/* Queue of operators */
typedef struct
{
  int size;           /* maximal number of operators      */
  int n;              /* number of operators in the queue */
  int first;          /* index of top element             */
  int last;           /* index of bottom element          */
  rp_operator** ptr;  /* array of pointers to operators   */
}
rp_oqueue_def;
typedef rp_oqueue_def * rp_oqueue;

#define rp_oqueue_size(q)    (q)->size
#define rp_oqueue_num(q)     (q)->n
#define rp_oqueue_first(q)   (q)->first
#define rp_oqueue_last(q)    (q)->last
#define rp_oqueue_ptr(q)     (q)->ptr
#define rp_oqueue_elem(q,i)  (q)->ptr[i]
#define rp_oqueue_empty(q)   (rp_oqueue_num(q)==0)

/* Construction of a queue of operators */
void rp_oqueue_create (rp_oqueue * q, int size);

/* Destruction of a queue of operators */
void rp_oqueue_destroy (rp_oqueue * q);

/* Enlarge the size of a queue */
void rp_oqueue_enlarge (rp_oqueue * q, int size);

/* Initialization of a queue --> empty */
void rp_oqueue_set_empty (rp_oqueue q);

/* Insertion of an operator in a queue */
void rp_oqueue_push (rp_oqueue q, rp_operator * o);

/* pop and return the top element */
rp_operator * rp_oqueue_pop (rp_oqueue q);

/* List of queues sorted by priorities */
typedef struct
{
  int size;           /* maximal number of queues                */
  int num;            /* number of operators in the queue        */
  int * priority;     /* priorities                              */
  rp_oqueue * queue;  /* queues of operators of given priorities */
}
rp_oqueue_list_def;
typedef rp_oqueue_list_def rp_oqueue_list[1];

#define rp_oqueue_list_size(q)        (q)[0].size
#define rp_oqueue_list_num(q)         (q)[0].num
#define rp_oqueue_list_ptrp(q)        (q)[0].priority
#define rp_oqueue_list_priority(q,i)  (q)[0].priority[i]
#define rp_oqueue_list_ptrq(q)        (q)[0].queue
#define rp_oqueue_list_elem(q,i)      (q)[0].queue[i]
#define rp_oqueue_list_empty(q)       (rp_oqueue_list_num(q)==0)

/* Creation of a priority queue */
void rp_oqueue_list_create (rp_oqueue_list * q);

/* Destruction of a priority queue */
void rp_oqueue_list_destroy (rp_oqueue_list * q);

/* q := empty set */
void rp_oqueue_list_set_empty (rp_oqueue_list q);

/* Every operator that can be inserted in the queue during propagator */
/* must be declared once by a call to this function                   */
void rp_oqueue_list_insert (rp_oqueue_list q, rp_operator * o);

/* Push a working operator in the priority queue during propagation */
void rp_oqueue_list_push (rp_oqueue_list q, rp_operator * o);

/* Pop a working operator from the priority queue during propagation */
rp_operator * rp_oqueue_list_pop (rp_oqueue_list q);

#ifdef __cplusplus
}
#endif

// ----------------
// Propagator class
// ----------------
class rp_propagator : public rp_operator
{
public:
  // Constructor
  rp_propagator(rp_problem * p, double improve = 10);

  // Destructor
  ~rp_propagator();

  // Operator virtual functions
  int priority() const;
  int arity() const;
  int var(int i) const;
  int pruned_arity() const;
  int pruned_var(int i) const;

  // Accessors and modifiers
  double improve() const;
  void set_improve(double x);

  // Insertion of an operator
  void insert(rp_operator * o);

  // Reduction of b using all the operators
  // Useful for the first propagation process
  int apply(rp_box b);

  // Reduction of b initially using only the operators depending on v
  // Useful during search when only one variable is split
  int apply(rp_box b, int v);

private:
  rp_problem * _problem;  /* the problem to be solved                       */
  int _id;                /* identifier of propagation process              */
  rp_vector _vop;         /* vector of all the operators                    */
  rp_dependency _dep;     /* dependency variables-operators                 */
  rp_oqueue_list _queue;  /* priority queue of operators                    */
  rp_box _bsave;          /* used to check domain modifications             */
  double _improve;        /* improvement factor controling propagation      */
                          /* percentage e.g. 10% --> propagation if domain  */
                          /* width reduced at least by a factor of 10%      */
  int _priority;          /* low priority if expensive application          */
  rp_intset _vars;        /* variables on which the propagator depends      */
  rp_intset _pruned_vars; /* variables that can be pruned by the propagator */

  // Copy protection
  rp_propagator(const rp_propagator& p);
  rp_propagator& operator=(const rp_propagator& p);

  // Application once the working operators have been defined
  int apply_loop(rp_box b);

  // Application of o only if the domain of some variable to be pruned
  // is not precise enough
  int check_precision(rp_operator * o, rp_box b);
};

#endif /* RP_PROPAGATOR */
