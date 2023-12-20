From Coq Require Import Compare_dec Lia PeanoNat 
 FunctionalExtensionality PropExtensionality.
From Corec Require Export Stream Haddock Exp.
Import Nat Lt Le.


Module Type Params.
Parameter T : Type.
Parameter p : T -> bool.
Parameter a : T.
Parameter non_p_a : p a = false. 
End Params.

Module filter_definition_and_properties(P:Params).
Import P.


Definition Filter(h : Stream T -> Stream T) (s: Stream T) : Stream T
:=
match (oracle (s = ppo_bot)) with
|left _ => ppo_bot
|right H  => if p (shead s H)
               then scons (shead s H) (h  (stail s))
               else h (stail s)
end.

Lemma Filter_mono :
is_monotonic 
  (P1 := EXP_Poset  (Stream T) (Stream T))
  (P2 := EXP_Poset  (Stream T) (Stream T))
 Filter.
 Proof.
intros f g Hle.
cbn in Hle.
unfold Filter.
intros s.
Opaque scons stail shead.
cbn.
cbn in f,g.
destruct (oracle
(@Logic.eq
   (@poset_carrier
      (ppo_poset
         (@cpo_ppo
            (@algebraic_cpo
               (@alg
                (Strm_PPO T)
                (Stream T))))))
   s
   (@ppo_bot
      (Stream T))));
             [apply poset_refl|].
destruct (p  (shead s n)); [|apply Hle].
specialize (scons_is_continuous (shead s n)) as Hc.
rewrite continuous_iff_mono_commutes in Hc.
destruct Hc as (Hm & _).
now apply Hm.
Qed.


Lemma single_fmap: forall S,
~is_empty S -> 
@single (Stream T)
  (@ppo_bot (Stream T)) =
@fmap (EXP (Stream T) (Stream T))
  (Stream T) S
  (fun
     _ : EXP (Stream T)
           (Stream T) =>
   @ppo_bot (Stream T)).
Proof.
intros S Hne.
rewrite not_empty_member in Hne.
destruct Hne as (x & Hmx).
apply set_equal.
split; intro Hm.
-
 rewrite member_single_iff in Hm.
 now exists x.
-
 destruct Hm as (f & Hf & Heq); subst.
 apply member_single.
Qed.  

Lemma fmap_proj: forall S s
(n : s <> ppo_bot),
@fmap (Stream T) (Stream T)
  (@proj (Stream T) 
     (Stream T) S (@stail T s))
  (@scons T (@shead T s n)) =
@fmap
  (EXP (Stream T) (Stream T))
  (Stream T) S
  (fun
     f : EXP (Stream T)
           (Stream T) =>
   @scons T (@shead T s n)
     (f (@stail T s))).
Proof.
intros S s Hn.
apply set_equal ; intro x; split; intro Hmx.
-
 destruct Hmx as (s' & (f & Hmf & Heq') & Heq); subst.
 now exists f.
-
 destruct Hmx as (f & Hf & Heq); subst.
 exists (f (stail s)); split; auto.
 now exists f.
Qed.  
  

Proposition Filter_is_H_continuous : is_H_continuous Filter.
Proof.
unfold is_H_continuous.
split; [apply Filter_mono | ].
intros S Hd.
extensionality s.
unfold Filter.
destruct (oracle (s = ppo_bot)).
-
 replace (fmap S
 (fun
    _ : EXP (Stream T)
          (Stream T) =>
  (@ppo_bot (Stream T)))) with (single (@ppo_bot (Stream T)));
    [now rewrite cpo_lub_single | ].
 apply single_fmap.
 now destruct Hd.
 -
  destruct (p (shead s n)) eqn: Heqn.
  +
   specialize (scons_is_continuous (shead s n) ) as Hc.
   unfold is_continuous in Hc.
   specialize (Hc (proj S (stail s)) 
     (@directed_proj _ _ S (stail s) Hd)).
   destruct Hc as (Hm & Hc).
   unfold commutes_with_lub in Hc.
   rewrite Hc.
   f_equal.
   apply fmap_proj.
 +
   f_equal.
Qed.

Definition filter := pointwise_fix Filter.


Lemma filter_least_fixpoint_of_Filter : 
is_least_fixpoint 
   (X := EXP_Poset (Stream T) (Stream T)) 
 Filter filter.  
Proof.
apply Haddock_pointwise,Filter_is_H_continuous.
Qed.


Lemma filter_bot: 
filter ppo_bot = ppo_bot.
Proof.
destruct (@filter_least_fixpoint_of_Filter) as (Hf & _).
unfold is_fixpoint in Hf.
rewrite <- Hf.
unfold Filter.
destruct (oracle (ppo_bot = ppo_bot)); auto.
exfalso;  now apply n.
Qed.


Lemma filter_keep: forall a s',
p a = true -> filter (scons a s') = scons a (filter s').
Proof.
intros a s' Ht.
destruct (filter_least_fixpoint_of_Filter) as (Hf & _).
unfold is_fixpoint in Hf.
remember (filter (scons a s')) as temp.
rewrite <- Hf in  Heqtemp.
rewrite Heqtemp.
unfold Filter.
destruct (oracle (scons a s' =  ppo_bot)).
-
  exfalso.
  now apply (scons_not_bot a s').
 -
  rewrite shead_scons.
  rewrite Ht.
  now rewrite stail_scons.
Qed.  


Lemma filter_throw: forall a s',
p a = false -> filter (scons a s') = filter s'.
Proof.
intros a s' Haf.
destruct (filter_least_fixpoint_of_Filter) as (Hf & _).
unfold is_fixpoint in Hf.
remember (filter (scons a s')) as temp.
rewrite <- Hf in  Heqtemp.
rewrite Heqtemp.
unfold Filter.
destruct (oracle (scons a s' = ppo_bot)).
-
  exfalso.
  now apply (scons_not_bot a s'). 
 -
  rewrite shead_scons.
  rewrite Haf.
  now rewrite stail_scons.
Qed.  


(*proving that filter is partial *)
Definition F_a_inf (s : Stream T) :=
   scons a s.

Lemma F_a_inf_cont : 
is_continuous (P1 := Stream T) (P2 := Stream T)  F_a_inf.
Proof.
apply scons_is_continuous.
Qed.

Definition a_inf := iterate_lub F_a_inf.

Lemma a_inf_fix: a_inf = scons a a_inf.
Proof.
specialize (Kleene _ F_a_inf_cont ) as Hk.
destruct Hk as (Hk & _).
unfold Haddock.is_fixpoint in Hk.
symmetry.
apply Hk.
Qed.

Lemma shead_a_inf : forall Hn,
shead a_inf Hn = a.
Proof.
intro Hn.
rewrite  shead_scons2 with (a := a) (s':= a_inf); 
[reflexivity | exact a_inf_fix].
Qed.

Lemma stail_a_inf : stail a_inf = a_inf.
Proof.
rewrite a_inf_fix at 1.
apply stail_scons.
Qed.
 
Lemma a_inf_total : is_total a_inf.
Proof.
apply (is_total_coind (A := T) (fun s =>  s = a_inf));
[| now unfold member].
intros s Hm.
unfold member in Hm; subst; split.
-
   intro Habs. 
   rewrite a_inf_fix in Habs.
   now apply scons_not_bot in Habs.
-
  unfold member.
  rewrite a_inf_fix at 1.
  now rewrite stail_scons.
Qed.

Lemma filter_a_inf_approx_bot : 
forall n, iterate (X := EXP_CPO (Stream T)(Stream T)) 
n Filter a_inf = ppo_bot.
Proof.
induction n; auto.
cbn.
unfold Filter in *.
destruct (oracle (a_inf = ppo_bot)); [reflexivity|].
rewrite shead_a_inf.
rewrite non_p_a.
now rewrite stail_a_inf.
Qed.

Lemma filter_a_inf_bot : filter a_inf = ppo_bot.
Proof.
unfold filter,pointwise_fix.
assert (Heqs : (fun b : Stream T =>
exists n : nat,
  b = iterate (X := EXP_CPO (Stream T)(Stream T))  n Filter a_inf) = single ppo_bot).
{
 apply set_equal; intro x ; split ; intro Hmx.
 -
   destruct Hmx as (n & Heq); subst.
   rewrite filter_a_inf_approx_bot.
   apply member_single.
 -  
   rewrite member_single_iff in Hmx; subst.
   now exists 0.
}
cbn in *.
rewrite Heqs.
apply cpo_lub_single.
Qed.  

(*proving that a restriction of filter is total*)

Lemma restrict_filter_total:
forall s, BoxDiamond p s -> is_total (filter s).
Proof.
intros s Hgf.
apply (is_total_coind (fun s =>  
exists s', BoxDiamond p s' /\ s = filter s'));
[| now exists s].
clear.
intros s (s' & Hm1 & Hm2).
rewrite BoxDiamond_unfold in Hm1.
destruct Hm1 as (Hf & Hgf).
revert s Hgf Hm2.
induction Hf; intros s Hgf Heqf.
-
 rewrite filter_keep in Heqf; auto.
 split.
 +
  rewrite Heqf.
  apply scons_not_bot.
 +
   exists s'.
   rewrite stail_scons in Hgf; split; auto.
   rewrite Heqf.
   now rewrite stail_scons.
-
 rewrite stail_scons in Hgf.
 rewrite filter_throw in Heqf; auto.
 apply BoxDiamond_stail in Hgf.
 now apply IHHf.
Qed.

End filter_definition_and_properties.
