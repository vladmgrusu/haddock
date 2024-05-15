From Coq Require Import Compare_dec Lia PeanoNat List
 FunctionalExtensionality PropExtensionality IndefiniteDescription.
From Corec Require Export Tree Haddock Lists.
Import Nat ListNotations.



Definition Mirror(f : RoseTree -> RoseTree): 
 RoseTree -> RoseTree
 := rtree ° (revb ° ((mapb f) ° rforest)).



 Lemma mapb_monotonic_in_func{P1 P2: CPO} : forall (f g:P1->P2),
 (forall x, f x <= g x) ->
 forall l, 
 List_le (mapb f l) (mapb g l).
 Proof.
 intros f g Ha l.
 destruct l ; [ | apply List_le_refl].
 destruct l ; [apply List_le_refl|].
 cbn.
 constructor.
 -
   cbn.
   now do 2 rewrite map_length.
 -
   cbn.
   rewrite map_length.
   intros i Hlt.
   destruct i; [apply Ha |].
   rewrite nth_indep with (d' := f ppo_bot);
     [|  rewrite map_length;lia].
  rewrite map_nth. 
  rewrite nth_indep with (d' := g ppo_bot);
  [| rewrite map_length; lia].
  rewrite map_nth.  
  apply Ha.
 Qed.
 

Lemma Mirror_is_monotonic :
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



Lemma Mirror_is_H_continuous : is_H_continuous Mirror.
Proof.
split; [apply Mirror_is_monotonic|].
intros S Hd.
extensionality t.
unfold Mirror.
destruct (rose_tree_cases_alt t) as [Hbot | (l & Heql)]; subst.
-
 unfold "°".
 rewrite rforest_extends_forestb; [| apply bot_is_compact].
 replace
   (@rev_inj Tree_PPO RoseTree(@ppo_bot RoseTree)) with tbot;
 [| symmetry; rewrite (@rev_inj_iff Tree_PPO RoseTree);
 [apply @inject_bot | apply bot_is_compact]].
 rewrite @inject_bot.
 cbn.
 rewrite  fmap_const_single; [| now destruct Hd].
 now rewrite cpo_lub_single.
-
remember ((fun f : EXP RoseTree RoseTree
  =>
  (rtree
   ° (revb ° (mapb f ° rforest)))
    (rtree
       (list_inj RoseTree l)))) as F.
  unfold "°" in HeqF.
  rewrite rforest_rtree in HeqF.
  assert (HcF : 
  @is_continuous (EXP_CPO RoseTree RoseTree) RoseTree F).  
  {
    assert (Heqf':
    F = fun f => (rtree ° (revb ° (mapb f))) (list_inj _ l))
     by now subst; auto.
    clear HeqF.
    subst.
    apply comp_is_continous; [apply rtree_is_continous|].
    replace ((fun f : EXP RoseTree RoseTree =>
    (revb ° mapb f)
      (list_inj RoseTree l))) with 
     (revb ° 
     ((fun f : EXP RoseTree RoseTree =>  mapb f
     (list_inj _ l)))
     ); auto.
    apply
     (@comp_is_continous 
     (EXP_CPO RoseTree RoseTree) 
     (RoseForest) 
     (RoseForest)); [apply revb_is_continuous|].
    apply  mapb_continuous_in_func.
  }
  destruct HcF with (S := S); [exact Hd |].
  cbn in H0.
  unfold "°".
  rewrite <- H0, HeqF.
  now rewrite rforest_rtree.
Qed.


Definition mirror : RoseTree -> RoseTree := 
   pointwise_fix Mirror.


Lemma mirror_least_fixpoint_of_Mirror : 
is_least_fixpoint 
   (X := EXP_Poset (RoseTree) (RoseTree)) 
 Mirror mirror.  
Proof.
intros.
apply Haddock_pointwise,Mirror_is_H_continuous.
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
unfold Mirror, "°".
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
unfold Mirror, "°".
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
total t -> total (mirror t).
Proof.
intros t Hw. 
apply (total_coind (fun t =>  
exists t',total t' /\ t = mirror t'));
[| now exists t].
intros t' Hm.
destruct Hm as (t'' & Hmt'' & Heq); subst.
rename t'' into t', Hmt'' into Hmt'.
specialize  Hmt' as Hmt''.
rewrite total_unfold in Hmt'.
destruct Hmt' as (Hne & Ha).
destruct (rose_tree_cases t') as [Habs | (f & Hnef & Heq)];
 [exfalso ; apply Hne; rewrite Habs; now rewrite <- inject_bot|subst].
split.
-
 rewrite <- mirror_fixpoint_eq.
 unfold Mirror, "°".
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
 unfold Mirror, "°" in Hin.
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


  


