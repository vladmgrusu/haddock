From Coq Require Import Compare_dec Lia PeanoNat List
 FunctionalExtensionality PropExtensionality IndefiniteDescription.
From Corec Require Export Tree Haddock Lists.
Import Nat Lt Le ListNotations.


Definition Mirror(f : RoseTree -> RoseTree): 
 RoseTree -> RoseTree
 := rtree ° (revb ° ((mapb f) ° rforest)).

Lemma Mirror_mono :
is_monotonic 
  (P1 := EXP_Poset RoseTree RoseTree)
  (P2 := EXP_Poset RoseTree RoseTree)
 Mirror.
Proof.
intros f g Hle.
cbn in Hle.
unfold Mirror.
intros s.
Opaque rtree rforest.
unfold "°".
apply rtree_is_monotonic.
apply revb_is_monotonic.
now apply  mapb_monotonic_in_func.
Qed.

(**
Lemma F_cont : forall (g : conat -> A -> B),
(forall a,
is_continuous (P1 := conat_CPO) (P2 := B)
(fun n => (g n) a))
->
(forall a, 
 is_continuous (P1 := conat_CPO) (P2 := B)
(fun n => F  (g n ) a)).
Proof.
intros g Hac a.
rewrite continuous_iff_mono_commutes; split.
{
  intros x y Hle.
  apply F_mono.
  intros a'.
  specialize (Hac a').
  rewrite continuous_iff_mono_commutes in Hac.
  destruct Hac as (Hm & _).
  now apply Hm.
}
intros C k Hd Hl.
split.
{
  intros x Hmx.
  destruct Hmx as (z & Hmz & Heq); subst.
  apply F_mono.
  intro a'.
  specialize (Hac a').
  rewrite continuous_iff_mono_commutes in Hac.
  destruct Hac as (Hm & _).
  apply Hm.
  destruct Hl as (Hul &_).
  now apply Hul.
}
intros t Hut.
assert (Hut' : forall c, member C c -> F (g c) a <=  t).
{
  intros c Hm.
  apply Hut.
  now exists c.
}
clear Hut.
unfold F, "°" in *.
cbn in *.
specialize Hd as Hd'.
destruct Hd' as (Hne & _).
rewrite not_empty_member in  Hne.
destruct Hne as (n & Hmn).
specialize (Hut' _ Hmn) as Humn.
destruct (rose_tree_cases_alt t) as [Heq | (L & Heq)]; subst.
{
  rewrite le_bot_iff_eq in *.
  apply rtree_is_bot,revb_is_bot,mapb_is_bot in Humn.
  rewrite Humn.
  cbn.
  rewrite rtree_extends_treeb; [| apply @bot_is_compact].
  cbn [treeb].
  replace (@rev_inj Forest_PPO RoseForest (list_bot A)) with 
  (@ppo_bot Forest_PPO); auto ;
   [apply @inject_bot |].
  symmetry.
  rewrite rev_inj_iff; [|apply @bot_is_compact].
  apply  @inject_bot.
}
 clear Humn.
 apply rtree_is_monotonic.
 assert (Hut : forall c : conat,
 member C c ->
   List_le (revb
      (mapb (g c)
         (rforest a)))
   (list_inj RoseTree
      L)) by 
  (intros c Hmc;
  specialize (Hut' _ Hmc);
  now apply rtree_is_rev_monotonic in Hut').
 clear Hut'.
 remember (rforest a) as F.
 destruct F; cbn; [| apply List_le_bot].
 replace L with (rev (rev L)) in * by now rewrite rev_involutive.
 assert (Hle :
 List_le (list_inj A  (map (g k) l)) (list_inj RoseTree (rev L))).
 {
  apply preservers_cont_aux with (C := C); auto.
  intros c Hmc.
  specialize (Hut _ Hmc).
  inversion Hut; subst.
  remember (rev L) as L'.
  remember (length l) as ll.
  do 2 rewrite rev_length in H1.
  constructor; auto.
  rewrite rev_length, map_length in *.
  intros i Hlt.
  unfold A in *.
  destruct ll;
  [  rewrite <- Heqll in Hlt ;lia |].

  assert (Hlt' : length l - S i < length l) by lia.
  specialize (H2 _ Hlt').
  rewrite rev_nth in H2; [| now rewrite map_length].
  rewrite rev_nth in H2; [| now rewrite <- H1].
  rewrite map_length, <- H1 in H2.
  now replace (length l -
  S (length l - S i)) with i in H2 by lia.
 }
 {
  inversion Hle; subst.
  rewrite map_length, rev_length in H1.
  constructor.
  -
   repeat rewrite rev_length.
   now rewrite map_length.
  -
    rewrite map_length in H2.
    rewrite rev_length, map_length.
    intros i Hlt.
    rewrite rev_nth; [| now rewrite map_length].
    rewrite rev_nth; [| now rewrite rev_length, <- H1].
    rewrite map_length, rev_length, <- H1.
    apply H2; lia.
 }
Qed. 

 
Lemma F_comp : forall (h : A -> B),
 (forall a, is_compact (h a)) ->
 (forall a, is_compact (F h a)).
Proof.
unfold F, "°", A, B.  
intros h Ha a.
rewrite inject_compacts.
cbn.
remember (rforest a) as F.
destruct F.
{
  cbn.
  assert 
    (Hal: forall i, i < length l -> 
    is_compact (h ((nth i l ppo_bot)))) by
    (intros i Hlt; apply Ha).
  assert 
    (Hall: forall i, i < length l -> 
       exists t:Tree, h (nth i l ppo_bot) =
          @inject Tree_PPO RoseTree t).
  {
    intros i Hlt.
    specialize (Hal _ Hlt).
    now rewrite inject_compacts in Hal.
  }
  clear Hal.
  assert (Hal :
  forall (j : BELOW (length l)), exists t, 
  h (nth (nval  _ j)  l ppo_bot) = inject t).
  {
    intros (j & Hlt).
    cbn.
    destruct (Hall _ Hlt).
    now exists x.
}
clear Hall.
apply functional_choice in Hal.
destruct Hal as (f & Hallf).
cbn in f.
remember (EXP2list (length l) f) as l'.
remember (fun t => 
   @rev_inj Tree_PPO RoseTree 
    (h (@inject Tree_PPO RoseTree t))) as h'.
exists (treeb (list_inj _ (rev (l')))).
cbn; subst.
assert (Heq': (list_inj RoseTree (rev (map h l))) =
rforest (@inject Tree_PPO RoseTree
(tree
(rev (EXP2list (length l) f)))));
   [| now rewrite Heq', rtree_rforest].  
rewrite rforest_extends_forestb; [| apply inject_compact].
rewrite rev_inj_inject.
f_equal.
cbn.
f_equal.
repeat rewrite rev_length,map_length.
rewrite rev_length, length_EXP2list.
apply nth_ext with (d := ppo_bot)(d' := ppo_bot).
-
 now rewrite  rev_length, map_length, length_EXP2list.
-  
 intros i Hlt.
 rewrite rev_nth; rewrite rev_length, map_length in *; auto.
 rewrite nth_EXP2LIST with (Hi := Hlt).
 unfold list2EXP.
 cbn.
 remember (length l) as ll.
 destruct ll; try lia.
 rewrite Heqll in *.
 erewrite nth_indep with (d' := h ppo_bot); [| rewrite map_length; lia].
 rewrite map_nth.
 rewrite rev_nth; [| rewrite length_EXP2list; lia].
 rewrite length_EXP2list.
 assert (Hlt' : S ll - S i < S ll) by lia.
 rewrite nth_EXP2LIST with (Hi := Hlt').
 now specialize (Hallf {|
  nval := S ll - S i;
  is_below := Hlt'
|}) . 
}
{
  exists tbot.
  rewrite mapb_bot.
  cbn.
  now rewrite rtree_bot,<- inject_bot.
}  
Qed.
End MirrorFunctional.

Import MirrorFunctional.
Module Import  MirrorDef := FuncDefMod MirrorFunctional.

Definition Mirror :
  (RoseTree -> RoseTree)-> RoseTree -> RoseTree := F.
Definition mirror : RoseTree -> RoseTree := f.


Lemma mirror_least_fixpoint_of_Mirror : 
is_least_fixpoint 
   (X := EXP_Poset (RoseTree) (RoseTree)) 
 Mirror mirror.  
Proof.
intros.
apply f_is_least_fixpoint_of_F.
Qed.


Lemma mirror_fixpoint_eq : 
 Mirror mirror = mirror. 
Proof.
intros.
destruct  mirror_least_fixpoint_of_Mirror as (Hf & _).
apply Hf.
Qed.


Lemma mirror_bot : mirror ppo_bot = ppo_bot.
Proof.
destruct (mirror_least_fixpoint_of_Mirror) as (Hf & _).
unfold is_fixpoint in Hf.
rewrite <- Hf.
unfold Mirror, F, "°".
rewrite rforest_bot.
cbn [mapb revb].
apply rtree_bot.
Qed.


Lemma mirror_list_aux : 
forall (l: list RoseTree), mirror (rtree (list_inj _ l)) = 
rtree (revb (mapb mirror (list_inj _ l))).
Proof.
intro l.
destruct (mirror_least_fixpoint_of_Mirror) as (Hf & _).
unfold is_fixpoint in Hf.
rewrite <- Hf.
unfold Mirror, F, "°".
repeat f_equal.
-
  rewrite <- Hf at 1.
  extensionality t.
  reflexivity.
-
  now rewrite rforest_rtree.
Qed.    


Lemma mirror_list : 
forall (l: list RoseTree), mirror (rtree (list_inj _ l)) = 
rtree (list_inj _ (rev (map mirror l))).
Proof.
intro l.
rewrite mirror_list_aux.
f_equal.
Qed.    

Lemma mirror_bot_iff : forall t, mirror t = ppo_bot <-> t = ppo_bot.
Proof.
intro t; split; intro Heq; subst.
-
 destruct (rose_tree_cases t) as [Habs | (f & Hnef & Heqf)]; subst; auto.
 destruct f as [l |].
 +
   rewrite mirror_list in Heq.
   exfalso.
   now apply (rtree_nbot  (rev (map mirror l))).
+
  exfalso.
  now apply Hnef.
-
  apply mirror_bot.
Qed.  

Lemma mirror_list_inv : forall t l, 
mirror t = rtree (list_inj _ l) -> exists l', 
t = rtree (list_inj _ l') /\ l = rev (map mirror l').
Proof.
intros t l Heq.
destruct (rose_tree_cases t) as [Habs | (f & Hnef & Heqf)]; subst; auto.
-
 exfalso.
 rewrite mirror_bot in Heq.
 now apply (rtree_nbot l).
-
 destruct f as [l'|].
 +
  rewrite mirror_list in Heq.
  apply rtree_injective in Heq.
  injection Heq; clear Heq; intro Heq.
  exists l';repeat split; auto.
 +
  exfalso; now apply Hnef.  
Qed.







Lemma mirror_total : forall t, 
is_well_formed t -> is_well_formed (mirror t).
Proof.
intros t Hw. 
apply (is_well_formed_coind (fun t =>  
exists t',is_well_formed t' /\ t = mirror t'));
[| now exists t].
intros t' Hm.
destruct Hm as (t'' & Hmt'' & Heq); subst.
rename t'' into t', Hmt'' into Hmt'.
specialize  Hmt' as Hmt''.
rewrite is_well_formed_unfold in Hmt'.
destruct Hmt' as (Hne & Ha).
destruct (rose_tree_cases t') as [Habs | (f & Hnef & Heq)];
 [exfalso ; apply Hne; rewrite Habs; now rewrite <- inject_bot|subst].
split.
-
 rewrite <- mirror_fixpoint_eq.
 unfold Mirror, F, "°".
 rewrite rforest_rtree in *.
 unfold mapb.
 destruct f; [clear Hnef| exfalso; now apply Hnef].
 cbn [revb Inb] in *.
 replace (@inject  _ RoseTree tbot) with (@ppo_bot RoseTree).
  +
     apply @rtree_nbot.
  +   
    symmetry.
    replace tbot with (@ppo_bot Tree_PPO); auto.
    apply inject_bot.
-
 intros t' Hin.
 rewrite <- mirror_fixpoint_eq in Hin.
 unfold Mirror, F, "°" in Hin.
 repeat rewrite rforest_rtree in *.
unfold mapb in  Hin.
destruct f; [clear Hnef| exfalso; now apply Hnef].
 cbn [revb Inb] in *.
rewrite <- in_rev, in_map_iff in Hin.
destruct Hin as (r & Heq & Hin).
exists r; split; auto.
Qed.


Lemma mirror_involutive : forall t, mirror (mirror t) = t.
Proof.
intro t.
remember (mirror (mirror t)) as t'.
symmetry.
rewrite bisim_iff_eq in *.
revert t t' Heqt'.
apply bisim_coind.
intros t t' Heqt.
rewrite bisim_unfold in Heqt.
destruct Heqt as [ (Heqt' & Heqt) |
 (l & l' & Heql & Heqt & Heqm & Hall)]; subst.
-
  repeat rewrite mirror_bot_iff in Heqt.
  subst.
  constructor.
-
  apply mirror_list_inv in Heqm.
  destruct Heqm as (l'' & Heqm & Heql''); subst.
  rewrite rev_length, map_length in Heql.
  apply mirror_list_inv in Heqm.
  destruct Heqm as (l''' & Heqm & Heql'''); subst.
  rewrite rev_length, map_length in Heql.
  rename l''' into l'.
  rewrite map_rev, rev_involutive in Hall.
  constructor; auto.
  intros n Hlt.
  rewrite <- Heql in Hlt.
  specialize (Hall _ Hlt).

  rewrite map_map in Hall.
  replace ((fun x : RoseTree => mirror (mirror x))) with 
   (mirror°mirror) in Hall; auto.
  replace 
    ((@nth RoseTree n
          (@map RoseTree RoseTree
          (mirror ° mirror) l')(@ppo_bot RoseTree))) with 
    ((@nth RoseTree n
         (@map RoseTree RoseTree
       (mirror ° mirror) l') 
          ((mirror°mirror) (@ppo_bot RoseTree)))) in Hall; 
   [|repeat f_equal;  unfold "°"; now repeat rewrite mirror_bot].
now rewrite map_nth in Hall.
Qed.
*)

  


