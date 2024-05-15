From Coq Require Import Compare_dec Lia PeanoNat
 FunctionalExtensionality IndefiniteDescription PropExtensionality.
From Corec Require Export FunComp Coind Algebraic.
Import Nat.


Inductive Strm (A:Type) : Type   :=
|sbot : Strm A
|scns : A -> Strm A -> Strm A.

Arguments sbot {_}.
Arguments scns {_} _ _.


Inductive Strm_le{A:Type} : Strm A -> Strm A -> Prop :=
|sbot_le : forall (s: Strm A), Strm_le  sbot  s
|scns_le : forall (a:A) (s  s': Strm A),
Strm_le  s s' -> Strm_le (scns a s) (scns a s').



Lemma Strm_le_refl{A:Type} : forall (s:Strm A), Strm_le s s.
Proof.
induction s; now constructor.       
Qed. 

Lemma Strm_le_trans{A:Type} : forall (s1 s2 s3 :Strm A), 
Strm_le s1 s2 -> Strm_le s2 s3 -> Strm_le s1 s3.
Proof.
intros s1 s2 s3 Hle.
revert s3.
induction Hle; intros t3 Hle'; [constructor|].
inversion Hle'; subst; clear Hle'.
constructor.
now apply IHHle.
Qed.

Lemma Strm_le_antisym{A:Type} : forall (s1 s2: Strm A),
Strm_le s1 s2 -> Strm_le s2 s1 -> s1 = s2.
Proof.
intros s1 s2 Hle1 Hle2.
induction Hle1; inversion Hle2; subst; auto.
f_equal.
now apply IHHle1.   
Qed.


Definition Strm_Poset (A:Type) : Poset :=
{|
  poset_carrier := Strm A;
  poset_le := Strm_le;
  poset_refl :=  Strm_le_refl;
  poset_trans := Strm_le_trans;
  poset_antisym := Strm_le_antisym  
|}.    

Definition Strm_PPO (A:Type) : PPO :=
{|
  ppo_poset := Strm_Poset A;
  ppo_bot := sbot;
  ppo_bot_least := sbot_le
|}.    

Definition Stream (A:Type) : COMPLETION (Strm_PPO A ):= 
    ideal_completion (Strm_PPO A).

Lemma scns_mono{A:Type}: forall a, 
is_monotonic (P1 := Strm_PPO A) (P2 := Strm_PPO A) (scns a).
Proof.
intros a x y Hle; constructor; auto.
Qed.


(**
Definition flift_scns{A:Type}(a: A) := 
@flift (Strm_ A)  (Strm_PPO A)
{|
func := scns a : Strm_PPO A -> Strm_PPO A; 
func_mono  := scns_mono a
|} (Stream A) (Stream A).
*)

Definition scons{A:Type}(a: A) : Stream A -> Stream A := 
  funcomp_bot_ext _ (scns_mono a) _ _.
  

Lemma scons_extends_scns{A:Type}(a: A) :
  forall cc, is_compact cc ->
  scons a cc = inject ((scns a: _ -> (Strm_PPO A)) (rev_inj cc)).
Proof. 
intros cc Hc.
now apply funcomp_bot_ext_ext.
Qed.
  

Lemma scons_is_continuous{A:Type}(a: A) : is_continuous (scons a).
Proof.
apply funcomp_bot_ext_cont.
Qed.
  

Lemma scons_is_monotonic{A:Type}(a: A) : is_monotonic (scons a).
Proof.
specialize (scons_is_continuous a) as Hc.
rewrite continuous_iff_mono_commutes in Hc.
now destruct Hc.
Qed.
  

  


Lemma scons_injective_1_aux{A:Type}(a a': A) (s s': Stream A): 
scons a s <= scons a' s' -> a = a'.
Proof.
intro Hle.
replace s with (cpo_lub (compacts_le s)) in Hle;
[| now rewrite algebraic_lub].
replace s' with (cpo_lub (compacts_le s')) in Hle;
[| now rewrite algebraic_lub].
destruct
  (scons_is_continuous a (compacts_le s) (algebraic_dir s)) 
  as (Hd & Heq).
destruct
(scons_is_continuous a' (compacts_le s') (algebraic_dir s')) 
as (Hd' & Heq').
rewrite  Heq, Heq' in Hle.
rewrite <- forallex_iff_lelub in Hle; auto.
{
 destruct Hd as (Hne & Hd).
 assert (Hex : (exists x : Stream A,
 member
   (fmap (compacts_le s) (scons a)) x)) by
  (now rewrite <- not_empty_member).
destruct Hex as (x & Hmx).
destruct (Hle _ Hmx) as (y & Hmy & Hlexy).
destruct Hmx as (u & Hmu & Hequ); subst.
destruct Hmy as (v & Hmv & Heqv); subst.
rewrite scons_extends_scns in  Hlexy; 
[|now destruct Hmu].
rewrite scons_extends_scns in  Hlexy; 
[|now destruct Hmv].
rewrite <- inject_bimono in Hlexy.
inversion Hlexy; now subst.
}
intros x Hmx.
destruct Hmx as (u & (Hcu & _) & Hequ); subst.
rewrite inject_compacts in *.
destruct Hcu as (p & Heqp); subst.
exists (scns a p).
rewrite scons_extends_scns; 
 [| apply inject_compact].
 now rewrite rev_inj_inject.
Qed. 



Lemma scons_rev_mono{A:Type}(a: A) : is_rev_monotonic (scons a).
Proof.
intros x y Hle.
unfold scons,funcomp_bot_ext,funcomp in Hle.
cbn in Hle.
rewrite <- forallex_iff_lelub in Hle; 
try apply algebraic_dir.
{ 
  replace x with (cpo_lub (compacts_le x));
  [| now rewrite algebraic_lub].
  replace y with (cpo_lub (compacts_le y));
  [| now rewrite algebraic_lub].
  cbn in *.
  apply forallex_lelub; try apply algebraic_dir.

  intros u (Hc & Hle'); subst.
  specialize (Hle (scons a u)).
  assert (Hm:  member
  (fmap (@compacts_le (@Stream A) x)
     (@bot_ext  (@Strm_PPO A) (@Strm_PPO A) (scns a) (@Stream A)(@Stream A)))
  (scons a u) ).
  {
   exists u; repeat split; auto.
   unfold bot_ext.
   destruct  (oracle (is_compact u)); 
   [clear i| exfalso; now apply n].
   now apply scons_extends_scns.
  }
 specialize (Hle Hm); clear Hm.
 destruct Hle as (v & Hmv & Hle).
 destruct Hmv as (k & Hmk & Heq); subst.
 rewrite  scons_extends_scns in Hle; auto.
 unfold bot_ext in Hle.
 destruct  (oracle (is_compact k)); 
 [| exfalso; now destruct Hmk].
 rewrite <- inject_bimono in Hle.
 cbn in Hle.
 inversion Hle; subst.
 destruct Hmk as (Hck & Hlek).
 exists k; repeat split ; auto.
 replace u with 
 (@inject  _ (@Stream A)(rev_inj u));
 [| rewrite inject_rev_inj]; auto.
 replace k with 
 (@inject  _ (@Stream A)(rev_inj k));
 [| rewrite inject_rev_inj]; auto.
  now rewrite <- inject_bimono.
}
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros u v (Hc & _) (Hc' & _) Hle'.
  unfold bot_ext.
  destruct (oracle (is_compact u)); auto;
  destruct (oracle (is_compact v)); try apply poset_refl;
  try apply ppo_bot_least.
  - 
   rewrite <- inject_bimono.
   apply scns_mono.
   now rewrite <- rev_inj_bimono.
  -
   contradiction.
}
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros u v (Hc & _) (Hc' & _) Hle'.
  unfold bot_ext.
  destruct (oracle (is_compact u)); auto;
  destruct (oracle (is_compact v)); try apply poset_refl;
  try apply ppo_bot_least.
  - 
   rewrite <- inject_bimono.
   apply scns_mono.
   now rewrite <- rev_inj_bimono.
  -
   contradiction.
 
}
{
  clear Hle.
  intros u (z & (Hc & Hle) & Heq); subst.
  unfold bot_ext.
  destruct  (oracle (is_compact z)); 
  [| exfalso; now apply n].
  apply inject_compact.
}
Qed.




Lemma scons_injective_2{A:Type}(a:A) : is_injective (scons a).
Proof.
intros x y Heq.
apply poset_antisym.
-
  apply (scons_rev_mono a).
  rewrite Heq.
  apply poset_refl.
-
  apply (scons_rev_mono a).
  rewrite Heq.
  apply poset_refl.    
Qed.


Lemma scons_injective{A:Type}(a a': A) (s s': Stream A): 
scons a s = scons a' s' -> a = a' /\ s = s'.
Proof.
intro Heq; split.
-
 eapply scons_injective_1_aux;  rewrite Heq;
 apply poset_refl.
-
  replace a' with a in Heq.
  +
    rewrite scons_injective_2; eauto.
  +
    eapply scons_injective_1_aux;  rewrite Heq;
    apply poset_refl.
Qed.




Definition stl{A:Type}(s:Strm A) : Strm A :=
match s with
sbot => sbot
|scns _ s' => s'
end.

Lemma stl_mono{A:Type}: 
@is_monotonic (Strm_PPO A) (Strm_PPO A) stl.
Proof.
intros x y Hle.
inversion Hle; subst; cbn; auto.
constructor.
Qed.



Definition stail{A:Type} : Stream A -> Stream A := 
  funcomp_bot_ext _ stl_mono _ _.
  
  
Lemma stail_extends_stl{A:Type}:
forall (cc: @Stream A), is_compact cc ->
stail cc = @inject _ (Stream A ) (stl (@rev_inj _ (Stream A) cc)).
Proof.
intros cc Hc.
now apply funcomp_bot_ext_ext.
Qed.

Lemma stail_is_continuous{A:Type} : 
@is_continuous (Stream A) (Stream A) stail.
Proof.
apply funcomp_bot_ext_cont.
Qed.


Lemma stail_is_monotonic{A:Type}: is_monotonic (@stail A).
Proof.
specialize (@stail_is_continuous A) as Hc.
rewrite continuous_iff_mono_commutes in Hc.
now destruct Hc.
Qed.

Lemma stail_scons{A:Type}: forall (a:A) (s : Stream A),
stail (scons a s) = s.
Proof.
intros a s.
assert (Heqf : stail ° (scons a) = id).
{
apply unique_continous_ext.
- 
 apply comp_is_continous.
 + apply stail_is_continuous.
 + apply scons_is_continuous.
- 
 apply id_is_continuous.
-
 intros cc Hc.
 unfold "°".
 rewrite scons_extends_scns; auto.
 rewrite stail_extends_stl; [|apply inject_compact].
 rewrite rev_inj_inject.
 cbn.
 now rewrite inject_rev_inj.
}
replace (stail (scons a s)) with ((stail ° scons a) s); auto.
now rewrite Heqf.
Qed.

Lemma scons_not_bot{A:Type}: 
forall a s, scons a s <> (@ppo_bot (Stream A)).
Proof.
intros a s Heq.
assert (Hle : scons a s <= ppo_bot)
 by (rewrite Heq ; apply poset_refl); clear Heq.
replace  (@inject _ (Stream A) sbot) with (@ppo_bot (Stream A)) in Hle; 
[| now rewrite @inject_bot].
replace s with (cpo_lub (compacts_le s)) in Hle;
[| now rewrite @algebraic_lub].
destruct(scons_is_continuous a (compacts_le s)) 
as (Hd & Heq); [apply algebraic_dir |].
rewrite Heq in Hle; clear Heq.
specialize (cpo_lub_prop _ Hd) as Hlu.
destruct Hlu as (Hu & _).
specialize (Hu (scons a ppo_bot)).
assert (Hm : member(fmap
   (compacts_le s)
   (scons a))
(scons a ppo_bot)) by
  (exists ppo_bot; repeat split; auto;
  [apply bot_is_compact | apply ppo_bot_least]).
specialize (Hu Hm).
assert (Habs : scons a ppo_bot <= ppo_bot) by
 (eapply poset_trans; eauto).
 replace  (@ppo_bot (Stream A))  with (@inject _ (Stream A) sbot) in Habs; 
 [| now rewrite <-  @inject_bot].
 rewrite scons_extends_scns in Habs; [| apply inject_compact].
 rewrite rev_inj_inject in Habs.
 rewrite <- inject_bimono in Habs.
 inversion Habs.
 Qed.


Lemma stail_as_lub{A:Type}:
forall (s: Stream A),
 (stail s) = cpo_lub (fmap (compacts_le s) stail).
Proof.
intro s.
specialize (algebraic_lub s) as Hlu.
remember (stail s) as t.
rewrite Hlu in Heqt.
destruct (stail_is_continuous (compacts_le s) (algebraic_dir s) ) as 
(Hd & Heqs).
now subst.
Qed.


Lemma stail_bot{A:Type} : stail (@ppo_bot (Stream A)) = ppo_bot.
Proof.
replace (@ppo_bot (Stream A)) with (@inject  _ (Stream A)sbot); 
[| apply @inject_bot].
rewrite  stail_extends_stl; [| apply inject_compact].
f_equal.
now rewrite rev_inj_inject.
Qed.


Lemma compacts_le_eq_aux{A:Type}:
forall (s: Stream A)(c:Strm A) (a:A),
member (compacts_le s) (@inject _ (Stream A) (scns a c))
->
forall x, member (compacts_le s) x ->
 x <> (@inject _ (Stream A) sbot) ->
 exists y,  x = @inject _ (Stream A) (scns a y).
Proof.
intros s c a Hm x Hmx Hne.
specialize (algebraic_dir s) as Hd.
remember (compacts_le s) as K.
destruct Hd as (_ & Hd).
specialize (Hd _ _ Hm Hmx).
destruct Hd as (z & Hmz & Hle1z & Hle2z).
remember Hmz as Hmz'.
replace z with (@inject  _ (Stream A)(rev_inj z)) in *; 
[| rewrite inject_rev_inj in *; auto]; [|subst;now destruct Hmz].
rewrite  <- inject_bimono in Hle1z.
inversion Hle1z; subst.
rewrite <- H2 in Hle2z.
remember Hmx as Hmx'.
replace x with (@inject  _ (Stream A)(rev_inj x)) in *; 
[| rewrite inject_rev_inj in *; auto]; [| now destruct Hmx'].
rewrite  <- inject_bimono in Hle2z.
inversion Hle2z; subst.
-
  exfalso.
  apply Hne.
  now rewrite H1.
-
  now exists s0.
Qed.


Lemma compacts_le_eq{A:Type}:
forall (s: Stream A)(c:Strm A) (a:A),
member (compacts_le s) (@inject _ (Stream A) (scns a c))->
(remove (compacts_le s) (@inject _ (Stream A) sbot))  = (fmap (fmap
   (compacts_le s) stail) (scons a)).
Proof.
intros s c a Hm.
specialize (compacts_le_eq_aux s c a Hm) as Hal.
apply set_equal ; intro x ; split.
-
intros (Hmx & Hne).
 destruct (Hal _ Hmx) as (y & Heqy); subst; auto.
 exists (@inject _ (Stream A) y); split.
 +
  exists (@inject  _ (Stream A) (scns a y)); split; auto.
  rewrite stail_extends_stl; [|now destruct Hmx].
  now rewrite rev_inj_inject.
 +
  rewrite scons_extends_scns; [| now apply inject_compact].
  now rewrite rev_inj_inject.
-
  intro Hmx.
  split.
  +
  destruct Hmx as (z & Hmz & Heq); subst.
  destruct Hmz as (w & Hmw & Heq); subst.
  rewrite stail_extends_stl; [|now destruct Hmw].
  rewrite scons_extends_scns; [| now apply inject_compact].
  rewrite rev_inj_inject.
  destruct (oracle (w = @inject _ (Stream A)sbot)); subst.
  *
  rewrite rev_inj_inject.
  cbn.
  split; [apply inject_compact|].
  destruct Hm as (Hcm & Hlem).
  eapply poset_trans; eauto.
  rewrite <- inject_bimono.
  do 2 constructor.
  *
  destruct (Hal _ Hmw n) as (x & Heq); subst.
  now rewrite rev_inj_inject.
+
  destruct Hmx as (z & Hmz & Heq); subst.
  destruct Hmz as (w & Hmw & Heq); subst.
  rewrite stail_extends_stl; [|now destruct Hmw].
  rewrite scons_extends_scns; [| now apply inject_compact].
  rewrite rev_inj_inject.
  intro Habs.
  apply inject_injective in Habs.
  discriminate.
Qed.   
 


Lemma stream_cases{A:Type}:
  forall (s:Stream A),  s = ppo_bot \/ 
  exists a, s = scons a (stail s).
Proof.  
intro s.
destruct (oracle 
(compacts_le s = single (ppo_bot))).
{
left.
specialize (algebraic_lub  s) as l.
unshelve erewrite is_lub_eq_cpo_lub  with 
(S' := single  (ppo_bot)) in l; 
[subst; apply cpo_lub_single | subst ; apply algebraic_dir 
|subst ; apply single_is_directed |].

rewrite <- e.
apply cpo_lub_prop.
apply algebraic_dir.
}
right.
remember (compacts_le s) as K.
assert (Hnek: ~is_empty K).
  {rewrite not_empty_member.
  exists (ppo_bot).
  subst.
  split.
  - 
    apply bot_is_compact.
  - 
    apply ppo_bot_least.     
  }
eapply not_empty_not_single_2dif in Hnek; eauto.
destruct Hnek as (y & Hm & Hne).
subst.
remember (rev_inj y) as u; cbn in u.
symmetry in Hequ.
rewrite rev_inj_iff in Hequ;  [|now destruct Hm].
destruct u; [rewrite <- Hequ in Hne; exfalso;  apply Hne; 
now rewrite <- inject_bot|].
exists a.
specialize (stail_as_lub s) as Heq.
rewrite Heq.
destruct (scons_is_continuous a (fmap (compacts_le s) stail)) as
   (Hd' & Heq').
{
  apply monotonic_directed; [apply stail_is_monotonic | apply algebraic_dir]. 
}
rewrite Heq'.
specialize (algebraic_lub  s) as Heq''.
rewrite Heq'' at 1.
 assert (Heqs : (remove (compacts_le s)  (@inject _ (Stream A) sbot)) = (fmap (fmap
   (compacts_le s) stail) (scons a))) by
  (apply compacts_le_eq with (c:= u);
  now rewrite Hequ).
rewrite <- Heqs.
apply is_lub_eq_cpo_lub; [apply algebraic_dir | | ].
-
 
 rewrite (inject_bot (P := Strm_PPO A)).
 apply remove_bot_directed with (x := y); auto.
 apply algebraic_dir.
-
  rewrite (inject_bot (P := Strm_PPO A)).
  rewrite <- is_lub_remove_bot.
  +
    apply cpo_lub_prop.
    apply algebraic_dir.
  +
    rewrite not_empty_member.
    now exists y.
  +  
    intro Heqt.
    rewrite Heqt in *.
    contradiction.
Qed.

    


Definition shead{A:Type} (s: Stream A)
   (Hne : s <>  ppo_bot) : A :=
match  (cases (stream_cases s)) with
|left H => False_rect _ (Hne H)
|right H => proj1_sig (constructive_indefinite_description _ H)
end.

Lemma shead_scons{A:Type}: 
forall (a:A)(s: Stream A) prf, shead (scons a s) prf = a.
Proof.
intros a s Hp.
unfold shead.
case_eq ( cases
(stream_cases
   (scons a s))).
-
  intros.
  exfalso.
  now apply Hp.
-
 intros.
 destruct ((constructive_indefinite_description
 (fun a0 : A =>
  scons a s = scons a0 (stail (scons a s))) e)).
 cbn.
 apply scons_injective in e0.
 now destruct e.
 Qed.


Lemma shead_scons2{A:Type}: 
 forall (a:A)(s s': Stream A) (Heq: s = scons a s' )prf, 
 shead s prf = a.
Proof.
intros.
subst.
apply shead_scons.
Qed.

Lemma scons_shead_stail{A:Type}: 
forall (s: Stream A) prf, 
s = scons (shead s prf) (stail s).
Proof.
intros s Hprf.
case_eq (cases (stream_cases s)); intros.
-
 exfalso.
 now apply Hprf.
-
 destruct e as (a & Heq).
 rewrite Heq at 1.
 f_equal.
 clear H.
 remember (stail s) as s'.
 symmetry.
 eapply shead_scons2; eauto.
Qed.




Lemma scns_scons{A:Type}:
forall (a:A)(x : Stream A)(s:Strm A),
is_compact x ->
scns a s = rev_inj x -> 
x = scons a (@inject (Strm_PPO  A) (Stream A)s).
Proof.
intros a x s Hc Heq.
assert (Heq' : 
(@inject (Strm_PPO  A) (Stream A) (scns a s)) = 
(@inject (Strm_PPO  A) (Stream A) (rev_inj x))); [now f_equal |].
rewrite inject_rev_inj in Heq'; auto.
rewrite <- Heq'.
rewrite scons_extends_scns; [| apply inject_compact].
do 2 f_equal.
now rewrite rev_inj_inject.
Qed. 
  
Lemma is_compact_stail{A:Type}: 
forall (s : Stream A),
is_compact s -> is_compact (stail s).
Proof.
intros s Hc.
replace s with (@inject (Strm_PPO  A) (Stream A) (rev_inj s));
[| rewrite inject_rev_inj; auto].
remember (rev_inj s) as t.
revert s Hc Heqt.
destruct t; intros s Hc Heqt.
-
  replace sbot with (@ppo_bot (Strm_PPO A)); auto.
  rewrite inject_bot.
  rewrite stail_bot.
  apply bot_is_compact.
-
 specialize (scns_scons a s t0 Hc Heqt) as Heqx.
 rewrite Heqt.
 rewrite inject_rev_inj; auto.
 rewrite Heqx.
 rewrite stail_scons.
 apply inject_compact.
Qed. 


Lemma is_compact_scons{A:Type}: 
forall (a:A)(s : Stream A),
is_compact s -> is_compact (scons a s).
Proof.
intros a s Hc.
rewrite scons_extends_scns; auto.
apply inject_compact.
Qed.


   
Definition _is_total{A:Type}(P: Setof (Stream A)) :=
 fun s => s <> ppo_bot /\ P (stail s).


Lemma _is_total_mono{A:Type} : 
is_monotonic (P1 := @to_poset (Stream A) Prop_poset)
(P2 := @to_poset (Stream A) Prop_poset) 
_is_total.
Proof.
intros T1 T2 Hle s (Hne & Hwf).
unfold _is_total in *.
cbn in Hle, T1, T2; split; auto.
Qed. 

Definition is_total{A:Type} (s: Stream A) :=
gfp (L := Pred_semilattice) _ _is_total_mono s.


Lemma is_total_unfold{A:Type}: forall (s: Stream A), 
is_total s <-> 
s <> ppo_bot /\ is_total (stail s).
Proof.
intros .
specialize (@Pred_unfold _ _ (_is_total_mono (A:=A))) as Hfu.
assert (Hi : @gfp
(@Pred_semilattice (Stream A))_ _is_total_mono s <->
_is_total (@gfp (@Pred_semilattice (Stream A)) _
   _is_total_mono) s); auto.
split ; intro Hx.
 + now rewrite <- Hfu.
  + symmetry in Hfu.
  now rewrite <- Hfu.
Qed.


Lemma is_total_coind{A:Type}: forall (S:Setof (Stream A)),
(forall s, 
 member S s -> s <> ppo_bot /\
 member S (stail s)) ->
(forall s, member S s -> is_total s).
Proof.
intros S Hall.
apply pred_coind.
intros s Hm.
now apply Hall.
Qed. 



Definition _Box{A:Type}(p : A -> bool)
(P: Setof (Stream A)) :=
 fun s => s = ppo_bot  \/ 
 exists a s', s = scons a s' /\ p a = true /\
  P s'.


Lemma _Box_mono{A:Type}(p : A -> bool) : 
is_monotonic (P1 := @to_poset (Stream A) Prop_poset)
(P2 := @to_poset (Stream A) Prop_poset) 
(_Box p).
Proof.
intros T1 T2 Hle s Hg.
inversion Hg ; subst; [now constructor|].
destruct H as (a & s' & Heq' & Hp & HT); subst.
constructor 2.
exists a, s'; repeat split; auto.
now apply Hle.
Qed. 

Definition Box{A:Type} (p : A -> bool)
(s: Stream A) :=
gfp (L := Pred_semilattice) _ (_Box_mono p)  s.


Lemma Box_unfold{A:Type}(p: A -> bool): 
forall (s: Stream A),  Box p s <-> 
(s = ppo_bot  \/ 
 exists a s', s = scons a s' /\ p a = true /\
  Box p s').
Proof.
intro s.
specialize (@Pred_unfold _ _ (_Box_mono p (A:=A))) as Hfu.
assert (Hi : @gfp
(@Pred_semilattice (Stream A))_ (_Box_mono p) s <->
(_Box p) (@gfp (@Pred_semilattice (Stream A)) _
   (_Box_mono p)) s); auto.
split ; intro Hx.
- now rewrite <- Hfu.
- symmetry in Hfu.
  now rewrite <- Hfu.
Qed.


Lemma Box_coind{A:Type}(p:A -> bool): 
forall (S:Setof (Stream A)),
(forall s, 
 member S s -> (s = ppo_bot  \/ 
 exists a s', s = scons a s' /\ p a = true /\
  member S s')) ->
(forall s, member S s -> Box p s).
Proof.
intros S Hall.
apply pred_coind.
intros s Hm.
now apply Hall.
Qed.


Inductive Diamond{A:Type}(p:A-> bool): Stream A -> Prop :=
|now : forall a s',  p a = true -> Diamond p (scons a s')
|later : forall a s',
 p a = false -> Diamond p s' -> Diamond p (scons a s').

Definition _BoxDiamond{A:Type}(p : A -> bool)
(P: Setof (Stream A)) :=
 fun s => Diamond p s /\ P (stail s).


Lemma _BoxDiamond_mono{A:Type}(p : A -> bool) : 
is_monotonic (P1 := @to_poset (Stream A) Prop_poset)
(P2 := @to_poset (Stream A) Prop_poset) 
(_BoxDiamond p).
Proof.
intros T1 T2 Hle s (Hne & Hwf).
unfold _BoxDiamond in *.
cbn in Hle, T1, T2; split; auto.
Qed. 

Definition BoxDiamond{A:Type} (p : A -> bool)
(s: Stream A) :=
gfp (L := Pred_semilattice) _ (_BoxDiamond_mono p)  s.


Lemma BoxDiamond_unfold{A:Type}(p: A -> bool): 
forall (s: Stream A),  BoxDiamond p s <-> 
Diamond p s  /\ BoxDiamond p (stail s).
Proof.
intros .
specialize (@Pred_unfold _ _ (_BoxDiamond_mono p (A:=A))) as Hfu.
assert (Hi : @gfp
(@Pred_semilattice (Stream A))_ (_BoxDiamond_mono p) s <->
(_BoxDiamond p) (@gfp (@Pred_semilattice (Stream A)) _
   (_BoxDiamond_mono p)) s); auto.
split ; intro Hx.
- now rewrite <- Hfu.
- symmetry in Hfu.
  now rewrite <- Hfu.
Qed.


Lemma BoxDiamond_coind{A:Type}(p:A -> bool): 
forall (S:Setof (Stream A)),
(forall s, 
 member S s -> Diamond p s /\
 member S (stail s)) ->
(forall s, member S s -> BoxDiamond p s).
Proof.
intros S Hall.
apply pred_coind.
intros s Hm.
now apply Hall.
Qed.


Lemma BoxDiamond_stail{A:Type} (p : A -> bool):
forall s, BoxDiamond p s -> BoxDiamond p (stail s).
Proof.
intros s Hgf.
destruct (stream_cases s) as [Heq | (a & Heq)]; subst.
-
 replace (stail ppo_bot) with (@ppo_bot (Stream A)); auto.
 now rewrite stail_bot.
 -
   rewrite Heq,stail_scons.
   rewrite BoxDiamond_unfold in Hgf.
   now destruct Hgf.
Qed. 



(* coinductive version of order between Streams*)
Inductive _sle{A:Type} (R: Stream A -> Stream A -> Prop): 
Stream A -> Stream A -> Prop :=
|_sle_bot : forall s, _sle R ppo_bot s
|_sle_scons : forall a s s', R s s' -> _sle R (scons a s) (scons a s').

Lemma _sle_mono{A:Type}: 
is_monotonic (P1 := binary_poset) (P2 := binary_poset) 
(@_sle A).
Proof.
intros R R' Hle x y Hsle.
inversion Hsle; subst.
-
  constructor.
-
   constructor.
   now apply (Hle s s').
Qed.       

Definition sle{A:Type} (s s': Stream A) :=
gfp (L := binary_semilattice) _ (_sle_mono)  s s'.

Lemma sle_unfold{A:Type}:
forall (s s': Stream A),  sle  s s' <-> 
(s = ppo_bot \/ exists a t t', s = scons a t /\ s' = scons a t' /\
 sle t t').
Proof.
intros.
specialize (@binary_unfold _ _ _ (@_sle_mono A )) as Hfu.
assert (Hi : @gfp
 (@binary_semilattice (Stream A) (Stream A)) _
  (_sle_mono ) s s' <->
 (_sle ) (@gfp (@binary_semilattice (Stream A) (Stream A)) _
    (_sle_mono )) s s') by (now rewrite <- Hfu).
 split ; intro Hx.
 - 
  unfold sle in Hx.
  rewrite Hi in Hx.
  replace (@gfp
  (@binary_semilattice
     (Stream A) (Stream A))
  (@_sle A) (@_sle_mono A)) with (@sle A) in Hx; auto.
  inversion Hx; subst.
  +
    now left.
  +
    right.
    now exists a,s0,s'0.
 -
   unfold sle.
   rewrite Hi.
   replace (@gfp
  (@binary_semilattice
     (Stream A) (Stream A))
  (@_sle A) (@_sle_mono A)) with (@sle A); auto.
  destruct Hx as [Hb | (a & t & t' & Heq1 & Heq2 & He3)];
   subst; now constructor.
Qed.

Lemma sle_coind{A:Type}: 
forall (R: binary (Stream A) (Stream A)),
(forall s s', 
 R s s' -> _sle R s s') ->
(forall s s', R s s' -> sle s s').
Proof.
intros S Hall.
apply binary_coind.
intros s Hm.
now apply Hall.
Qed.

Lemma sle_stail{A:Type}: forall s s': (Stream A),
sle s s' -> sle (stail s)(stail s').
Proof.
intros s s' Hle.
rewrite sle_unfold in Hle.
destruct Hle as [Heq | (a & t & t' & Heq1 & Heq2 & Heq3)];
 subst.
-
  rewrite stail_bot.
  rewrite sle_unfold.
  now left.
-
  now do 2 rewrite stail_scons.
Qed.    

Lemma le_sle{A:Type}: forall (s s' : Stream A), 
s <= s' -> sle s s'.
Proof.
apply sle_coind.
intros s s' Hle.
destruct (stream_cases s) as [Heq | (a & Heq)]; subst.
-
 constructor.
-
destruct (stream_cases s') as [Heq' | (a' & Heq')]; subst.
+
 rewrite le_bot_iff_eq in Hle; subst.
 constructor.
+
 rewrite Heq, Heq' in *.
 specialize Hle as Hle'.
 apply scons_injective_1_aux in Hle; subst.
 constructor.
 rewrite <- Heq, <- Heq' in *.
 now apply stail_is_monotonic.
Qed.


Lemma sle_le{A:Type}: forall (s s' : Stream A), 
sle s s' -> s <= s'.
Proof.
intros s s' Hsle.
replace s with (cpo_lub (compacts_le s));
[|now rewrite algebraic_lub].
replace s' with (cpo_lub (compacts_le s'));
[|now rewrite algebraic_lub].
rewrite <- forallex_iff_lelub;
[| apply algebraic_dir | apply algebraic_dir | now intros x (Hc & _) ].
intros x (Hc & Hle).
replace s with (cpo_lub (compacts_le s) ) in Hle;
   [|now rewrite algebraic_lub].
specialize Hc as Hc'.
assert (Hdd : is_directed (compacts_le s)) by now apply algebraic_dir.
specialize (Hc _ Hdd Hle).
destruct Hc as (c & (Hc & Hlec) & Hlex).
replace c with 
(@inject (Strm_PPO A)(Stream A)(rev_inj c)) in Hlex;
[|now rewrite inject_rev_inj].
replace x with 
  (@inject (Strm_PPO A)(Stream A)(rev_inj x)) in Hlex;
  [|now rewrite inject_rev_inj].
rewrite <- inject_bimono in Hlex.
remember (rev_inj x) as x'.
remember (rev_inj c) as c'.
clear Hle Hdd.
revert c x s s' Hsle Heqx' Heqc' Hlec Hc' Hc.
induction Hlex; intros  c x t t' Hsle Heqx' Heqc' Hlec Hc' Hc.
-
  exists ppo_bot.
  replace x with (@ppo_bot (Stream A)).
  +
    repeat split; 
    [apply bot_is_compact | apply ppo_bot_least | apply poset_refl].
  +
    symmetry in Heqx'.
    rewrite rev_inj_iff in Heqx'; auto.
    rewrite <- Heqx'.
    now rewrite <- inject_bot.
-
  assert (Hex:exists y : Stream A,
  member
     (compacts_le
         (stail t')) y /\
    stail x <= y).
    {
     apply  (IHHlex (stail c) (stail x) (stail t) (stail t')).
     *
       now apply sle_stail.
     *
       rewrite scns_scons with (a := a)(x := x)(s:=s);
        auto.
       now rewrite stail_scons, rev_inj_inject.
     * 
      rewrite scns_scons with (a := a)(x := c)(s:=s');
       auto.
      now rewrite stail_scons, rev_inj_inject.
     *  
      now apply stail_is_monotonic.
     * 
      now apply is_compact_stail.
     *
      now apply is_compact_stail.
    }
  clear IHHlex.
  destruct Hex as (y & (Hc'' & Hmle) & Hles).
  exists (scons a y); repeat split.
  +
    now apply is_compact_scons.
  +
    rewrite sle_unfold in Hsle.
    destruct Hsle as [Heq | (a' & t1 & t2 & Heq1 & Heq2 & Heq3)];
       subst.
    *
      rewrite le_bot_iff_eq in Hlec.
      subst.
      symmetry in Heqc'.
      rewrite rev_inj_iff in Heqc'; [| apply bot_is_compact].
      replace (@ppo_bot (Stream A)) with 
         (@inject (Strm_PPO A)(Stream A) (@ppo_bot (Strm_PPO A))) in
           Heqc'; [|now rewrite inject_bot].
      apply inject_injective in Heqc'.
      discriminate.
    *
      rewrite stail_scons in Hmle.
      replace a with a'; [now apply scons_is_monotonic|].
      specialize (scns_scons _ _ _ Hc Heqc') as Hx; subst.
      erewrite scons_injective_1_aux; eauto.
  +
    specialize (scns_scons _ _ _ Hc' Heqx') as Hx; subst.
    rewrite stail_scons in Hles.
    now apply scons_is_monotonic.
Qed.          


Lemma le_iff_sle{A:Type}: forall (s s' : Stream A), 
s <= s' <-> sle s s'.
Proof.
split; intro Hle.
-
 now apply le_sle.
-
 now apply sle_le.
Qed.

Lemma sle_refl{A:Type}: forall (s : Stream A), 
sle s s.
Proof.
intro s.
apply le_sle, poset_refl.
Qed.    

Lemma sle_trans{A:Type}: forall (s s' s'': Stream A), 
sle s s' -> sle s' s'' -> sle s s''.
Proof.
intros s s' s'' Hle1 Hle2.
rewrite <- le_iff_sle in *.
eapply poset_trans; eauto.
Qed.    


(*bisimulation*)
Inductive _bisim{A:Type} (R: Stream A -> Stream A -> Prop): 
Stream A -> Stream A -> Prop :=
|_bisim_bot : _bisim R ppo_bot ppo_bot
|_bisim_scons : forall a s s', R s s' -> _bisim R (scons a s) (scons a s').


Lemma _bisim_mono{A:Type}: 
is_monotonic (P1 := binary_poset) (P2 := binary_poset) 
(@_bisim A).
Proof.
intros R R' Hle x y Hb.
inversion Hb; subst.
-
  constructor.
-
   constructor.
   now apply (Hle s s').
Qed.       

Definition bisim{A:Type} (s s': Stream A) :=
gfp (L := binary_semilattice) _ (_bisim_mono)  s s'.

Lemma bisim_unfold{A:Type}:
forall (s s': Stream A),  bisim  s s' <-> 
((s = ppo_bot /\ s' = ppo_bot) \/
 exists a t t', s = scons a t /\ s' = scons a t' /\
 bisim t t').
Proof.
intros.
specialize (@binary_unfold _ _ _ (@_bisim_mono A )) as Hfu.
assert (Hi : @gfp
 (@binary_semilattice (Stream A) (Stream A)) _
  (_bisim_mono ) s s' <->
 (_bisim ) (@gfp (@binary_semilattice (Stream A) (Stream A)) _
    (_bisim_mono )) s s') 
    by (now rewrite <- Hfu).
 split ; intro Hx.
 - 
  unfold bisim in Hx.
  rewrite Hi in Hx.
  replace (@gfp
  (@binary_semilattice
     (Stream A) (Stream A))
  (@_bisim A) (@_bisim_mono A)) with (@bisim A) in Hx; auto.
  inversion Hx; subst.
  +
    now left.
  +
    right.
    now exists a,s0,s'0.
 -
   unfold bisim.
   rewrite Hi.
   replace (@gfp
  (@binary_semilattice
     (Stream A) (Stream A))
  (@_bisim A) (@_bisim_mono A)) with (@bisim A); auto.
  destruct Hx as [(Hb1 & Hb2) | (a & t & t' & Heq1 & Heq2 & He3)];
   subst; now constructor.
Qed.

Lemma bisim_coind{A:Type}: 
forall (R: binary (Stream A) (Stream A)),
(forall s s', 
 R s s' -> _bisim R s s') ->
(forall s s', R s s' -> bisim s s').
Proof.
intros S Hall.
apply binary_coind.
intros s Hm.
now apply Hall.
Qed.

Lemma bisim_refl{A:Type}: forall (s : Stream A), bisim s s.
intro s.
remember s as s'.
rewrite Heqs' at 1.
revert s s' Heqs'.
apply bisim_coind.
intros s s' Heq; subst.
destruct (stream_cases s) as [Heq | (a & Heq)]; 
rewrite Heq; now constructor.
Qed.


Lemma bisim_sym{A:Type}: forall (s s': Stream A), 
bisim s' s -> bisim s s'.
apply bisim_coind.
intros s s' Heq; subst.
rewrite bisim_unfold in Heq.
destruct Heq as [(Hb1 & Hb2) | (a' & t & t' & Heq1 & Heq2 & He3)]; 
  subst; now constructor.
Qed.



Lemma bisim_sle{A:Type}: forall (s s' : Stream A), 
bisim s s' -> sle s s'.
Proof.
apply sle_coind.
intros s s' Hb.
rewrite bisim_unfold in Hb.
destruct Hb as [(Hb1 & Hb2) | (a' & t & t' & Heq1 & Heq2 & He3)]; 
  subst; now constructor.
Qed.


Lemma bisim_sle'{A:Type}: forall (s s' : Stream A), 
bisim s s' -> sle s' s.
Proof.
intros s s' Hb.
apply bisim_sym in Hb.
now apply bisim_sle.
Qed.


Lemma sle_bisim{A:Type}: forall (s s' : Stream A), 
sle s s' -> sle s' s -> bisim s s'.
Proof.
intros s s' Hle1 Hle2.
apply sle_le in Hle1, Hle2.
assert (Heq : s = s') by (now apply poset_antisym); subst.
apply bisim_refl.
Qed.

Lemma bisim_eq{A:Type}: forall (s s' : Stream A),
bisim s s' -> s = s'.
intros s s' Hb.
apply poset_antisym.
-
 now apply sle_le, bisim_sle.
-
 now apply sle_le, bisim_sle'.
Qed.

Lemma eq_bisim{A:Type}: forall (s s' : Stream A),
s = s' -> bisim s s'.
Proof.
intros s s' Heq ; subst.
apply bisim_refl.
Qed.

Lemma bisim_iff_eq{A:Type} : forall (s s' : Stream A),
s = s' <-> bisim s s'.
Proof.
split; intro Heq.
- now apply eq_bisim.
- now apply bisim_eq.
Qed.



Lemma sle_antisym{A:Type} : forall (s s' : Stream A),
sle s s' -> sle s' s -> s = s'.
Proof.
intros s s' Hb1 Hb2.
rewrite bisim_iff_eq.
now apply sle_bisim.
Qed.


Lemma bisim_trans{A:Type} : forall (s s' s'' : Stream A),
bisim s s' -> bisim s' s'' -> bisim s s''.
Proof.
intros s s' s'' Hb1 Hb2.
rewrite <- bisim_iff_eq in *; now subst.
Qed.


  





