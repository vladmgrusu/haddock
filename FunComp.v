From Coq Require Import IndefiniteDescription 
FunctionalExtensionality ProofIrrelevance.
From Corec Require Export Completion.



Lemma funcomp_dir{A1 A2 : ALGEBRAIC}:
forall (f : A1 -> A2),
(forall cc : A1, is_compact cc -> is_compact (f cc)) ->
is_monotonic_on f (fun cc : A1 => is_compact cc) ->
forall x : A1, is_directed (fmap (compacts_le x) f).
Proof.
intros f Hac Hmo x.
unshelve eapply monotonic_on_directed.
-
intros u v  (Hcu & _) (Hcv & _) Hle.
apply Hmo; auto.
-
 apply algebraic_dir.
Qed.   

Definition funcomp{A1 A2:ALGEBRAIC}(f : A1 -> A2)
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)) : A1 -> A2 :=
fun x => cpo_lub (fmap (compacts_le x) f) .

Lemma funcomp_ext{A1 A2:ALGEBRAIC} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
forall cc, is_compact cc ->  
(funcomp f Hac Hmo) cc = f cc.
Proof.
intros f Hac Hmo cc Hcc.
unfold funcomp.
remember
(fun (xs : {x : A1  | is_compact x}) =>
exist  _ (f (proj1_sig xs)) (Hac _ (proj2_sig xs))) 
as fc.
remember (exist _ cc Hcc) as cc'.
specialize (lem50part2 
(D := compacts_ppo A1) (C := compacts_ppo A2) fc cc') as Hld.
assert (Hm' :      
is_monotonic_on (P1:=compacts_ppo A1) (P2 := compacts_ppo A2)fc (fun d' : compacts_ppo A1 =>
d' <= cc')).
{
 intros u v Hmu Hmv Hle.
 destruct u, v; cbn in *.
 subst.
 cbn.
 now apply Hmo.
}
specialize (Hld Hm').
clear Hm'.
assert (Hl : is_lub (fmap (compacts_le cc) f) (f cc)).
{
subst; cbn in *.
cbn in *.
split.
-
 intros x Hmx.
 destruct Hmx as (z & (Hcz & Hlez) & Heq);
 subst.
 apply Hmo; auto.
- 
 intros y Hu.
 destruct Hld as (Hu' & Hmin').
 cbn in *.
 apply Hu.
 exists cc; repeat split; auto.
 apply poset_refl.
}
specialize 
(cpo_lub_prop _ (funcomp_dir f Hac Hmo cc)) as Hl'.
eapply is_lub_unique with (x := f cc) in Hl'; auto.
Qed.


Lemma funcomp_mono{A1 A2:ALGEBRAIC} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
is_monotonic (funcomp f Hac Hmo).
Proof.
intros f Hac Hmo x y Hle.
unfold funcomp.
apply forallex_lelub.
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros  u v (Hc & _) (Hc' & _) Hle'.
  now apply Hmo.
}
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros  u v (Hc & _) (Hc' & _) Hle'.
  now apply Hmo.
}
intros u (v & (Hcv & Hlev)& Heq); subst.
exists (f v); split; [| apply poset_refl].
exists v; repeat split; auto.
eapply poset_trans; eauto.
Qed.


Lemma funcomp_ed_cont{A1 A2:ALGEBRAIC} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
is_ed_continuous (funcomp f Hac Hmo).
Proof.
intros f Hac Hmo.
intros gc g Hc Hle.
assert (Hd : is_directed (fmap (compacts_le g) f) ).
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros  u v (Hc1 & _) (Hc2 & _) Hle'.
  now apply Hmo. 
} 
specialize (Hc _ Hd Hle).
destruct Hc as (c & Hmc & Hlec).
destruct Hmc as (x & (Hcx & Hlex) & Heq); subst.
exists x; repeat split; auto.
eapply poset_trans; [now apply Hlec| ].
rewrite funcomp_ext; auto; apply poset_refl.
Qed.

Lemma funcomp_cont{A1 A2:ALGEBRAIC} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
is_continuous (funcomp f Hac Hmo).
Proof.
intros f Hac Hmo.
rewrite continuous_iff_ed_continuous_mono.
split.
-
apply funcomp_mono.
-
apply funcomp_ed_cont.
Qed.   


Definition bot_ext{P1 P2: PPO} (f: P1 -> P2)
(e1 : COMPLETION P1) (e2 : COMPLETION P2) : e1 -> e2 :=
 fun x => match (oracle (is_compact x)) with
 left _ =>  inject (f (rev_inj x))
 |right _ => ppo_bot
 end.

Program Definition funcomp_bot_ext{P1 P2: PPO} (f: P1 -> P2)
(Hm: is_monotonic f) (e1 : COMPLETION P1) (e2 : COMPLETION P2)
(x : e1) : e2 := funcomp (bot_ext f e1 e2) _ _ x.
Next Obligation.
intros.
unfold bot_ext.
destruct (oracle (is_compact cc)) as [Hc | n];
[| exfalso; now apply n].
apply inject_compact.
Qed.

Next Obligation.
intros.
intros u v Hmu Hmv Hle.
unfold member in Hmu,Hmv.
unfold bot_ext.
destruct (oracle (is_compact u)) as [_| n];
[|exfalso; now apply n].
destruct (oracle (is_compact v)) as [_| n];
[|exfalso; now apply n].
rewrite <- inject_bimono.
apply Hm.
rewrite <- rev_inj_bimono; auto.
Qed.
 

Lemma funcomp_bot_ext_mono{P1 P2:PPO}:
forall (m : P1 -> P2) (Hm: is_monotonic m)
(e1 : COMPLETION P1) (e2 : COMPLETION P2),
    is_monotonic 
      (funcomp_bot_ext m Hm e1 e2).
Proof.  
intros.  
unfold funcomp_bot_ext.
apply funcomp_mono.
Qed.  
 


Lemma funcomp_bot_ext_cont{P1 P2:PPO}:
forall (m : P1 -> P2) (Hm: is_monotonic m)
(e1 : COMPLETION P1) (e2 : COMPLETION P2),
    is_continuous 
      (funcomp_bot_ext m Hm e1 e2).
Proof.  
intros.  
unfold funcomp_bot_ext.
apply funcomp_cont.
Qed.  
 

Lemma funcomp_bot_ext_ext{P1 P2:PPO}:
forall (m : P1 -> P2) (Hm: is_monotonic m)
(e1 : COMPLETION P1) (e2 : COMPLETION P2),
forall (cc: e1) (Hc : is_compact cc),
(funcomp_bot_ext m Hm e1 e2) cc = inject (m (rev_inj cc)) . 
Proof.  
intros.  
unfold funcomp_bot_ext.
rewrite funcomp_ext; auto.
unfold bot_ext.
now destruct (oracle (is_compact cc)).
Qed.  




Lemma unique_continous_ext{P1 P2: PPO} 
  {e1 : COMPLETION P1}{e2 : COMPLETION P2}:
forall (f g : e1 -> e2),
is_continuous f -> 
is_continuous g -> (forall cc, is_compact cc ->f cc =  g cc) 
 -> f = g.
Proof.
intros f g Hcf Hcg Ha.
extensionality x.
replace x with (cpo_lub (compacts_le x)); 
[|now rewrite algebraic_lub].
unfold is_continuous in *.
destruct (Hcf _ (algebraic_dir x)) as (Hdf & Heq); 
rewrite Heq; clear Heq.
destruct (Hcg _ (algebraic_dir x)) as (Hdg & Heq); 
rewrite Heq; clear Heq.
apply cpo_lub_eq; auto.
apply set_equal ; intro y; split; intros (z & (Hc & Hle) & Heq); subst;
   exists z; repeat split; auto.
 now rewrite Ha.
Qed. 
  
   

