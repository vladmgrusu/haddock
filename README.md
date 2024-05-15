# Coq Development for JLAMP submission

This is the Coq code associated to our JLAMP submission **Formal Definitions and Proofs for Partial (Co)recursive Functions**.  The submission is available as a [technical report](https://inria.hal.science/hal-04360660v). "make" to compile. Please use Coq 8.19.1.


## Files

 * *Oracle.v* :  using appropriate axiom's from Coq's standard library, all propositions are decidable. Right from the start we will be using standard (non-constructive) mathematics.
 
 * *Sets.v*  : sets of a given type *T* are functions frop *T* to *Prop*. Contains basic facts about sets and mappings of functions on sets.
 
 * *Poset.v*: basic notions regarding partially-ordered sets and monotonic functions, including the notions of least upper bound (*lub*) and of directed set.
 
 * *Coind.v* : The Knaster-Tarski theorem for upper semi-lattices and its application to coinduction.
 
 * *PPO.v* : basic notions about pointed partial orders.
 
 * *CPO.v* : basic notions about Complete Partial Orders, compactness and continuity.
 
 * *Kleene.v* : Kleene's fixpoint theorem.
 
 * *Ideal.v* : the notion of ideal (directed, downward-closed set) of a PPO, and various properties (e.g., ideals form a CPO whose order is inclusion and whose compacts are the principal ideals).
 
 * *Algebraic.v* : the notion of algebraic CPO; ideals over a PPO form an algebraic CPO; the notion of $\epsilon\delta$-continuity and its equivalence to continuity for functions between algebraic CPOs.
 
 * *Completion.v* : the completion of a PPO is an algebraic CPO together with a bimonotonic bijection from the PPO to the compact elements of the algebraic CPO. Two concrete completions are defined: ideal completion, and the completion of the PPO of compacts of an algerbaic CPO being the algebraic CPO itself.
 
 * *Option.v* : the flat order of the option type, up to and including the fact that, as an algebraic CPO, it is a completion of itself seen as a PPO.

* *Exp.v* : the set of functions from a set to an algebraic CPO form an algebraic CPO whose compacts are functions having finite support and compact values.  If the domain is a finite set, the fact that the PPO of functions is completed to an algerbraic CPO whose compacts are exactly the compact-valued functions.

* *Sum.v* : the separated sum of  PPOs, CPOs, and algebraic CPOs is an order of the same kind as its summands. The sum of the completions of a set of PPOs is the completion of the sum of the PPOs in question.

* *Lists.v* : lists, first as sum of exponantials and then, isomorphically, as Coq lists plus a bottom element. Their organization as PPOs, CPOs, and algebraic CPOs of lists  that are completions of lists of the PPOs of lists of compact elements. Functions on lists (map, rev) and their continuity.

* *FunComp.v* : continuous functions between algebraic CPOs as unique completions of monotonic functions between the PPOs being the compacts of the algebraic CPOs in question.

* *Stream.v* : streams as completions of their finite approximations. Their constructors and destructors, the fact the (completed) constructors act as constructors of the completed streams.  Coinductive definitions of totality and bisimulation.

* *Tree.v* : same as previous item, but for Rose trees.

* *Haddock.v* : H-continuity and its equivalence to continuity, and Haddock's theorem.

* *Filter.v* : definition of the *filter* function on streams using Haddock's theorem. Proofs of properties as in the paper.

* *Mirror.v* : same as previous item but for *mirror* function on Rose trees.

* *Collatz.v* : using Haddock's theorem, defintion of a *collatz* function, and proof of a property stated in the paper.

* *While.v* : using Haddoc's theorem, definition of a partial monadic function modeling  imperative *while* loops.

* *Hoare.v* : Hoare logic for a shallow embedding of an imperative language in Coq. Includes the  proof of validity of the Hoare rule for *while* loops from the paper.
