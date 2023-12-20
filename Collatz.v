From Coq Require Import Compare_dec Lia PeanoNat 
 FunctionalExtensionality PropExtensionality.
From Corec Require Export  Option Exp Completion Haddock.
Import Nat Le.

Definition Succ(o:option nat) : option nat :=
  match o with
  | Some n => Some (S n)
  | None => None
  end.
  

Lemma Succ_mono : is_monotonic 
(P1 := option_Poset nat) (P2 := option_Poset nat) Succ.
Proof.
intros [n | ] [n' |] Hle; inversion Hle; subst; cbn;  constructor.
Qed.

Lemma Succ_cont : is_continuous
 (P1 := option_CPO nat) (P2 := option_CPO nat) Succ.
Proof.
apply continuous_iff_mono_commutes.
split; [apply Succ_mono|].
intros T l Hd (Hu & Hl).
split.
-
  intros x (z & Hlz & Heq); subst.
  now apply Succ_mono, Hu.
-
 intros y Huy.
 destruct l; [|cbn; constructor].
 rewrite (@option_directed nat) in Hd.
 destruct Hd as [(a & Heq) | (a & Heq)]; subst.
  +
     destruct (@is_lub_single (option_PPO nat)a) as (Hua & _).
     specialize (Hl _ Hua).
     inversion Hl; subst; clear Hl Hua.
     apply Huy.
     exists (Some n); split; auto.
     apply member_single.
  +
    destruct  (ordered_pair_has_lub
    (P := option_Poset nat) _ _ (None_le a)) as (Hua & _).
    specialize (Hl _ Hua).
    inversion Hl; subst; clear Hl Hua.
    apply Huy.
    exists (Some n); split; auto.
Qed.

Unset Printing Implicit.

Definition Collatz (f : option nat -> option nat) (x : option nat): option nat :=
match x with
None => None
| Some n => 
  if n =? 1 then Some 0 else
  if even n then Succ (f (Some (div2 n)))
 else  Succ (f (Some  (3*n+1)))
end.



Lemma Collatz_is_monotonic :
 is_monotonic
 (P1:=  EXP_Poset (option_Poset nat) (option_Poset nat))
 (P2:=  EXP_Poset (option_Poset nat) (option_Poset nat))
 Collatz.
Proof.
intros f g  Hle x.
unfold Collatz.
destruct x.
- 
 destruct (n =? 1) eqn: Heq1; [apply @poset_refl |].
 destruct (even n) eqn: Heqeven.
 +
  apply Succ_mono, Hle.
 + 
   apply Succ_mono, Hle.
-
  apply @poset_refl.
Qed.

Lemma Collatz_is_H_continuous :
 is_H_continuous
 (A:=  (option nat))
 (B:=  (option_CPO nat))
 Collatz.
Proof.
split; [apply Collatz_is_monotonic |].
intros S Hd.
extensionality x.
unfold Collatz.
destruct x.
- 
  destruct (n =? 1) eqn: Heq1.
  +
   Unset Printing Implicit.
   replace  (@fmap (EXP (option nat) (option_CPO nat))
       (option_CPO nat) S
       (fun _ : EXP (option nat) (option_CPO nat)
        => @Some nat 0)) with (single (Some 0)); 
    [ now rewrite @cpo_lub_single | ].  
   apply set_equal; intro x ; split; intro Hmx.   
   *
    rewrite member_single_iff in Hmx; subst.
    destruct Hd as (Hne & _).
    rewrite not_empty_member in Hne.
    destruct Hne as (f & Hmf).
    now exists f.
   *
    destruct Hmx as (f & Hmf & Heq); subst.
    apply member_single.
  +
   destruct (even n) eqn: Heqeven.
   *
   specialize Succ_cont as Hc.
   unfold is_continuous in Hc.
   specialize (Hc (proj S  (Some (div2 n)))
     (@directed_proj _ _ S  (Some (div2 n)) Hd)).
   destruct Hc as (Hm & Hc).
   rewrite Hc.
   f_equal.
   apply set_equal; intro x ; split; intro Hmx.   
   --
    destruct Hmx as (y & Hmy & Heq); subst.
    destruct Hm as (Hne & _).
    rewrite not_empty_member in Hne.
    destruct Hne as (x & Hmx).
    destruct Hmx as (z & Hmz & Heqz); subst.
    destruct Hmy as (u & Hmu & Heq); subst.
    destruct Hmz as (v& Hmv & Heq); subst.        
    now exists u.
  --
    destruct Hmx as (f & Hmf & Heq); subst.
    eexists (f (Some (div2 n))); split; auto.
    now exists f.
    *
     specialize Succ_cont as Hc.
     unfold is_continuous in Hc.
     specialize (Hc (proj S  (Some (3* n+1)))
     (@directed_proj _ _ S  (Some (3*n+1)) Hd)).
     destruct Hc as (Hm & Hc).
     rewrite Hc.
     f_equal.
      apply set_equal; intro x ; split; intro Hmx.   
      --
       destruct Hmx as (y & Hmy & Heq); subst.
       destruct Hm as (Hne & _).
       rewrite not_empty_member in Hne.
       destruct Hne as (x & Hmx).
       destruct Hmx as (z & Hmz & Heqz); subst.
       destruct Hmy as (u & Hmu & Heq); subst.
       destruct Hmz as (v& Hmv & Heq); subst.        
       now exists u.
     --
       destruct Hmx as (f & Hmf & Heq); subst.
       eexists (f (Some (3*n+1))); split; auto.
       now exists f.     
-
  Unset Printing Implicit.

  replace
    (@fmap (EXP (option nat) (option_CPO nat))
       (option_CPO nat) S
       (fun _ : EXP (option nat) (option_CPO nat) =>
        @None nat)) with (single (@ppo_bot (option_PPO nat)));
         [now rewrite @cpo_lub_single | ].
  apply set_equal; intro x ; split; intro Hmw.
  +
   rewrite member_single_iff in Hmw; subst.
   destruct Hd as (Hne & _).
   rewrite not_empty_member in Hne.
   destruct Hne as (f & Hnf).
   now exists f.
  +
   destruct Hmw as (f & Hmf & Heq); subst.
   apply member_single.
Qed.

Definition collatz := pointwise_fix (A:=  (option nat))
 (B:=  (option_CPO nat)) Collatz.

Lemma even_not_one :
forall n,even n = true ->  n =?1 = false.
Proof.
intros n Hnt.
rewrite eqb_neq.
intro Habs; subst.
discriminate.
Qed.   


Lemma collatz_zero : collatz (Some 0) = None.
Proof.
unfold collatz, pointwise_fix.
Abort.
   

