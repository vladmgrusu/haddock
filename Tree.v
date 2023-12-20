From Coq Require Import Compare_dec Lia PeanoNat List
 FunctionalExtensionality IndefiniteDescription Logic.Eqdep.
From Corec Require Export FunComp Lists Exp Coind.
Import Nat Lt Le ListNotations.


Inductive Tree : Type   :=
|tbot : Tree 
|tree : list Tree -> Tree.


Lemma Tree_induct : forall (P : Tree -> Prop),
    P tbot ->
    (forall l,
            (forall n, n < length l ->  P (nth n l tbot))
            -> P (tree l))  ->
    forall t,  P t.
Proof.
intros P Hn Hall.
fix Ftree_induct_t 1.
intro t.
destruct t.
*
 apply Hn.
*
  apply Hall.
  induction l; intros n Hlt;  cbn in Hlt ; [lia|].
  destruct n; cbn.
  +
    apply  Ftree_induct_t.
  +
    apply IHl ; lia.
Qed.

Inductive Tree_le : Tree -> Tree -> Prop :=
|tbot_le : forall t, Tree_le tbot t
|tree_le : forall l l', length l = length l' -> 
(forall n,
n < length l -> Tree_le (nth n l tbot) (nth n l' tbot)) -> 
Tree_le (tree l) (tree l').


Lemma Tree_le_refl : forall t,  Tree_le t t.
Proof.
intro t.        
induction t using Tree_induct; constructor; auto.
Qed. 

Lemma Tree_le_trans : forall t1 t2 t3, 
Tree_le t1 t2 -> Tree_le t2 t3 -> Tree_le t1 t3.
Proof.
intros t1 t2 t3 Hle.
revert t3.
induction Hle; intros t3 Hle; [constructor|].
inversion Hle; subst.
constructor; [congruence|].
intros n Hlt.
apply H1; auto.
apply H4.
now rewrite <- H.
Qed.

Lemma Tree_le_antisym : forall t1 t2,
Tree_le t1 t2 -> Tree_le t2 t1 -> t1 = t2.
Proof.
intros t1 t2 Hle1 Hle2.
induction Hle1; inversion Hle2; subst; auto.
f_equal.   
apply nth_ext with (d:= tbot)(d' := tbot); auto.
intros n Hlt.
apply H1; auto.
apply H5; lia.
Qed.


Definition Tree_Poset : Poset :=
{|
  poset_carrier := Tree;
  poset_le := Tree_le;
  poset_refl :=  Tree_le_refl;
  poset_trans := Tree_le_trans;
  poset_antisym := Tree_le_antisym  
|}.    

Definition Tree_PPO : PPO :=
{|
  ppo_poset := Tree_Poset;
  ppo_bot := tbot;
  ppo_bot_least := tbot_le
|}.    

Definition Forest := List Tree.
Definition Forest_PPO := List_PPO Tree_PPO.

Definition treeb(f :Forest): Tree :=
match f with 
 list_bot _ => tbot
|list_inj _ l => tree l
end.


Lemma treeb_monotonic : forall (f1 f2 : Forest),
List_le (P:=Tree_PPO)  f1 f2 -> Tree_le (treeb f1) (treeb f2).
Proof.
intros f1 f2 Hle.
inversion Hle; subst;constructor; auto.
Qed.



Definition forestb(t: Tree): Forest :=
match t with
tbot => list_bot _
| tree l => list_inj _ l
end.

Lemma forestb_monotonic : forall (t1 t2 : Tree),
Tree_le t1 t2 -> 
List_le (P:=Tree_PPO) (forestb t1) (forestb t2).
Proof.
intros t1 t22 Hle.
inversion Hle; subst;constructor; auto.
Qed.

Lemma treeb_forestb_id : treeb ° forestb = id.
Proof.
extensionality t.
unfold "°" , id.
destruct t; auto.
Qed.  

Lemma forestb_treeb_id : forestb °  treeb = id.
Proof.
extensionality f.
unfold "°" , id.
destruct f; auto.
Qed.  


Definition RoseTree : COMPLETION Tree_PPO := ideal_completion Tree_PPO.
Definition RoseForest : COMPLETION Forest_PPO := 
     List_completion _ RoseTree.


(*confirming that elements of RoseForest are lists of RoseTree*) 
Goal
((@poset_carrier (@cpo_ppo (@algebraic_cpo (alg RoseForest)))) = 
List RoseTree).
reflexivity.
Qed.     


Definition rtree := 
  funcomp_bot_ext (treeb: Forest_PPO -> Tree_PPO) 
  (treeb_monotonic) RoseForest RoseTree.  

Lemma rtree_extends_treeb : forall cc, is_compact cc ->
rtree cc = inject ((treeb: _ -> Tree_PPO) (rev_inj cc)).
intros cc Hc.
now apply funcomp_bot_ext_ext.
Qed.

Lemma rtree_is_continous : is_continuous rtree.
Proof.
apply funcomp_bot_ext_cont.
Qed.



Definition rforest := 
  funcomp_bot_ext (forestb: Tree_PPO -> Forest_PPO) 
  (forestb_monotonic) RoseTree RoseForest.  

Lemma rforest_extends_forestb : forall cc, is_compact cc ->
rforest cc = inject ((forestb: _ -> Forest_PPO) (rev_inj cc)).
intros cc Hc.
now apply funcomp_bot_ext_ext.
Qed.

Lemma rforest_is_continous : is_continuous rforest.
Proof.
apply funcomp_bot_ext_cont.
Qed.



Lemma rtree_rforest_id : 
(rtree : RoseForest -> RoseTree)° (rforest:RoseTree-> RoseForest) = 
(id :RoseTree -> RoseTree).
Proof.
apply unique_continous_ext.
-
  apply comp_is_continous.
  +
    apply rtree_is_continous. 
  +
    apply rforest_is_continous.
-
 apply id_is_continuous.
-
 intros cc Hc.
 unfold "°", id.  
 rewrite inject_compacts in Hc.
 destruct Hc as (p & Heq); subst.
 rewrite rforest_extends_forestb; [| apply inject_compact].
 rewrite rev_inj_inject.
 rewrite rtree_extends_treeb; [| apply inject_compact].
 f_equal.
 rewrite rev_inj_inject.
 destruct p ; auto.
Qed.


Lemma rtree_rforest : forall t, (rtree (rforest t)) = t.
Proof.
intro t.
replace (rtree (rforest t)) with ((rtree°rforest) t); auto.
now rewrite rtree_rforest_id.
Qed.

Lemma rforest_rtree_id : 
(rforest:RoseTree-> RoseForest) °(rtree : RoseForest -> RoseTree)   = 
(id :RoseForest -> RoseForest).
Proof.
apply unique_continous_ext.
-
  apply comp_is_continous.
  +
    apply rforest_is_continous. 
  +
    apply rtree_is_continous.
-
 apply id_is_continuous.
-
 intros cc Hc.
 unfold "°", id.
 rewrite inject_compacts in Hc.
 destruct Hc as (f & Heq); subst.
 rewrite rtree_extends_treeb; [| apply inject_compact].
 rewrite rev_inj_inject.
 rewrite rforest_extends_forestb; [| apply inject_compact].
 f_equal.
 rewrite rev_inj_inject.
 destruct f ; auto.
Qed.  
    


Lemma rforest_rtree : forall f, (rforest (rtree f)) = f.
Proof.
  intro f.
  replace (rforest (rtree f)) with ((rforest°rtree) f); auto.
  now rewrite rforest_rtree_id.
Qed.
  


Lemma rtree_injective : is_injective rtree.
Proof.
intros x y Heq.
replace x with ((rforest ° rtree) x); 
[| rewrite rforest_rtree_id; auto].
replace y with ((rforest ° rtree) y); 
[| rewrite rforest_rtree_id; auto].
unfold "°".
now rewrite Heq.
Qed.


Lemma rforest_injective : is_injective rforest.
Proof.
intros x y Heq.
replace x with ((rtree  ° rforest ) x); 
[| rewrite rtree_rforest_id; auto].
replace y with ((rtree ° rforest) y); 
[| rewrite rtree_rforest_id; auto].
unfold "°".
now rewrite Heq.
Qed.
 
Lemma rforest_is_monotonic : is_monotonic rforest.
Proof.
specialize rforest_is_continous as Hc.
rewrite continuous_iff_mono_commutes in Hc.
now destruct Hc.
Qed.
  

Lemma rtree_is_monotonic : is_monotonic rtree.
Proof.
specialize rtree_is_continous as Hc.
rewrite continuous_iff_mono_commutes in Hc.
now destruct Hc.
Qed.

Lemma rtree_is_rev_monotonic : is_rev_monotonic rtree.
Proof.
intros t t' Hle.  
replace t with ((rforest ° rtree) t); 
[| rewrite rforest_rtree_id; auto].
replace t' with ((rforest ° rtree) t'); 
[| rewrite rforest_rtree_id; auto].
unfold "°".
now apply rforest_is_monotonic.
Qed.


Lemma rforest_is_rev_monotonic : is_rev_monotonic rforest.
Proof.
intros f f' Hle.  
replace f with ((rtree ° rforest) f); 
[| rewrite rtree_rforest_id; auto].
replace f' with ((rtree ° rforest) f'); 
[| rewrite rtree_rforest_id; auto].
unfold "°".
now apply rtree_is_monotonic.
Qed.

  


Lemma rose_tree_cases:
  forall t,  t = ppo_bot \/ 
  exists f:RoseForest, f <> list_bot _ /\ t = rtree f.
Proof.  
intro t.
destruct (oracle (t = ppo_bot));
   [now left | right].
exists (rforest t); split.
-
  intro Heq.
  apply n; clear n.
  specialize (algebraic_lub  t) as Ha.
  specialize rforest_is_continous as Hc.
  specialize (Hc  _ (algebraic_dir t)).
  destruct Hc as (Hd & Heqr).
  rewrite Ha in Heq.
  rewrite Heq in Heqr.
  symmetry in Heqr.
  specialize  (cpo_lub_prop _ Hd) as (Hcu & _).
  rewrite Heqr in Hcu.
  clear Heqr.
  specialize Hd as Hd'.
  destruct Hd' as (Hne & _).
  apply lub_bot_implies_single_bot in Hne; auto.
  replace ppo_bot with (rforest ppo_bot) in Hne.
  {
    apply inj_fmap_single  with (f := rforest) (x := ppo_bot) in Hne.
    - 
      specialize (cpo_lub_prop _ (algebraic_dir t)) as Hcu'.
      rewrite Hne in Hcu' at 1. 
      rewrite <- Ha in Hcu'.
      specialize (is_lub_single (@ppo_bot RoseTree)) as Hl'.
      rewrite  (@is_lub_unique RoseTree 
      (single ppo_bot) _ _ Hcu' Hl').
      symmetry.
      unfold ppo_bot.
      replace tbot with (@ppo_bot Tree_PPO); auto.
    -
     apply rforest_injective.
 }
 {
    rewrite rforest_extends_forestb; [|apply bot_is_compact].
    replace (rev_inj ppo_bot) with (@ppo_bot Tree_PPO); auto.
    symmetry.
    rewrite rev_inj_iff; [|apply bot_is_compact].
    apply inject_bot.
 } 
-
  specialize (rtree_rforest_id) as Hi.
  unfold "°", id in Hi.
  assert (Heq: rtree (rforest t) = (fun x : RoseTree
    =>
    rtree
      (rforest x)) t ); auto.
    rewrite Hi in Heq.
    now rewrite Heq.
Qed.  
    
  
Lemma rtree_nbot : 
    forall l, rtree (list_inj _ l) <> ppo_bot.
Proof.
  intros l Heq.
  replace (@ppo_bot RoseTree) with (rtree (@ppo_bot RoseForest)) in Heq.
  - 
    apply rtree_injective in Heq.
     discriminate.
  -
    rewrite rtree_extends_treeb; [|apply @bot_is_compact].
    replace (@rev_inj _ RoseForest ppo_bot)
       with (@ppo_bot (List_PPO Tree_PPO)).
    +
      cbn.
      apply @inject_bot.
    +  
      symmetry.
      rewrite rev_inj_iff; [apply @inject_bot | apply bot_is_compact].
Qed.
  


Lemma rtree_is_bot : forall f,
 rtree f = ppo_bot -> f = list_bot _.
Proof.
intros f Heq.
destruct f; auto.
exfalso.
now apply (rtree_nbot l).
Qed.


Lemma rev_inj_tbot :
@rev_inj Tree_PPO RoseTree (@ppo_bot RoseTree) = tbot.
Proof.
rewrite rev_inj_iff; [| apply @bot_is_compact].
now rewrite @inject_bot.
Qed.

Lemma rev_inj_list_bot : @rev_inj Forest_PPO RoseForest
        (list_bot RoseTree) = list_bot Tree.
Proof.
rewrite rev_inj_iff; [| apply @bot_is_compact].
now rewrite @inject_bot.
Qed.

Lemma rtree_bot : rtree (list_bot _) = @ppo_bot RoseTree.
Proof.
rewrite rtree_extends_treeb; [|apply @bot_is_compact].
rewrite rev_inj_list_bot.
cbn [treeb].
now rewrite @inject_bot.
Qed.


Lemma rforest_bot : rforest (@ppo_bot RoseTree) = list_bot RoseTree.
Proof.
rewrite rforest_extends_forestb; [| apply @bot_is_compact].
rewrite rev_inj_tbot.
cbn [forestb].
now rewrite @inject_bot.
Qed.

Lemma rose_tree_cases_alt:
  forall t,  t = ppo_bot \/  exists l, t = rtree (list_inj _ l).
Proof.  
intro t.
destruct (rose_tree_cases t) as [Heq | (f & Hneq & Heq)]; subst;
[now left | right].
destruct f; [| exfalso; now apply Hneq].
now exists l. 
Qed.


Lemma rose_tree_eq_inv:
  forall t t',  t = t' ->
  (t = ppo_bot /\ t' = ppo_bot) \/  
   exists l l', length l = length l' /\
   t = rtree (list_inj _ l) /\ t' = rtree (list_inj _ l') /\
   forall i, i < length l -> nth i l ppo_bot = nth i l' ppo_bot.
Proof.  
intros t t' Heqtt'.
destruct (rose_tree_cases_alt t) as [Heq | (l & Heq)]; subst;
[now left | right].
exists l, l; repeat split; auto.
Qed.


Definition Inb (t : RoseTree) (l : List RoseTree ) :=
match l with
list_bot _ => False
|list_inj _ l' => In t l'
end. 

Definition _total(P : Setof RoseTree) : Setof RoseTree :=
fun t =>  
t <> @inject _ RoseTree tbot  /\
forall t',  Inb t' (rforest t)
-> P t'.

Lemma _total_mono: 
is_monotonic 
(P1 := @to_poset RoseTree Prop_poset)
 (P2 := @to_poset RoseTree Prop_poset) 
_total.
Proof.
intros x y Hle z Hwf.
cbn in *.
destruct Hwf as (Hne & Ha).
split; auto.
Qed.


Definition total (t: RoseTree) :=
gfp (L := Pred_semilattice) _ _total_mono t.

Lemma total_unfold: forall t, total t <-> 
t <> @inject _ RoseTree tbot  /\
forall t',  Inb t' (rforest t) -> total t'.
Proof.
intros t.
specialize (@Pred_unfold _ _ _total_mono) as Hfu.
assert (Hi : @gfp
(@Pred_semilattice RoseTree)_ _total_mono t <->
_total (@gfp (@Pred_semilattice RoseTree) _
   _total_mono) t); auto.
split ; intro Hx.
- now rewrite <- Hfu.
- symmetry in Hfu.
  now rewrite <- Hfu.
Qed.


Lemma total_coind: forall (S:Setof RoseTree),
(forall t, 
 member S t -> t <> @inject _ RoseTree tbot /\
 forall t', Inb t' (rforest t) -> member S t') ->
(forall t, member S t -> total t).
Proof.
intros S Hall.
apply pred_coind.
intros t Hm.
now apply Hall.
Qed. 


Definition nthb (n:nat) (l : List RoseTree ) : RoseTree :=
match l with
list_bot _ => ppo_bot
|list_inj _ l' => nth n l' ppo_bot
end. 


Definition lengthb (l : List RoseTree ) : nat :=
match l with
list_bot _ => 0
|list_inj _ l' => length l'
end. 

(* coinductive version of order between Rose Trees*)
Inductive _rle (R: RoseTree -> RoseTree -> Prop): 
RoseTree -> RoseTree -> Prop :=
|_rle_bot : forall t, _rle R ppo_bot t
|_rle_rtree :  forall (l l': list RoseTree), 
length l = length l' -> 
(forall n,
n < length l -> R (nth n l ppo_bot) (nth n l' ppo_bot)) -> 
_rle R (rtree (list_inj _ l)) (rtree (list_inj _ l')).


Lemma _rle_mono: 
  is_monotonic 
    (P1 := binary_poset) (P2 := binary_poset) 
  _rle.
Proof.
intros R R' Hle x y Hsle.
inversion Hsle; subst.
-
  constructor.
-
   constructor; auto.
   intros n Hlt.
   now apply (Hle (nth n l ppo_bot) (nth n l' ppo_bot)), H0.
Qed.       

Definition rle (t t': RoseTree) : Prop :=
gfp (L := binary_semilattice) _rle _rle_mono t t'.

Lemma rle_unfold: forall (t t': RoseTree), 
 rle  t t' <-> 
(t = ppo_bot \/ (exists (l l' : list RoseTree), length l = length l' /\
 t = rtree (list_inj _ l) 
/\ t' = rtree (list_inj _ l') /\
(forall n,
n < length l -> rle (nth n l ppo_bot) (nth n l' ppo_bot)))).
Proof.
intros t t'.
specialize (@binary_unfold _ _ _ (_rle_mono)) as Hfu.
assert (Hi : @gfp
(@binary_semilattice
   RoseTree
   RoseTree) _rle
_rle_mono  t t' <->
_rle
(@gfp
   (@binary_semilattice
      RoseTree
      RoseTree)
   _rle _rle_mono) t t')
    by (now rewrite <- Hfu).
 split ; intro Hx.
 - 
  unfold rle in Hx.
  rewrite Hi in Hx.
  replace (@gfp
  (@binary_semilattice
     RoseTree RoseTree)
  _rle _rle_mono) with rle in Hx; auto.
  inversion Hx; subst.
  +
    now left.
  +
    right.
    now exists l,l'.
 -
   unfold rle.
   rewrite Hi.
   replace (@gfp
  (@binary_semilattice
     RoseTree RoseTree)
  _rle _rle_mono) with rle; auto.
  destruct Hx as [Hb | (l & l' & Heq1 & Heq2& Heq3 & Heq4  )];
   subst; now constructor.
Qed.

Lemma rle_coind: 
forall (R: binary RoseTree RoseTree),
(forall t t', 
 R t t' -> _rle R t t') ->
(forall t t', R t t' -> rle t t').
Proof.
intros S Hall.
apply binary_coind.
intros s Hm.
now apply Hall.
Qed.



Lemma le_rle: forall t t',
t<= t' -> rle t t'.
Proof.
apply rle_coind.
intros t t' Hle.
destruct (rose_tree_cases t) as [Heq | (f & Hd & Heq)]; subst.
-
 constructor.
-
destruct (rose_tree_cases t') as [Heq' | (f' & Hd' & Heq')]; subst.
+
 rewrite le_bot_iff_eq in Hle.
 rewrite Hle.
 constructor.
+
 specialize Hle as Hle'.
 apply rtree_is_rev_monotonic in Hle; subst.
 inversion Hle; subst; auto.
  * exfalso; now apply Hd.
  *
    constructor; auto.
Qed.




Lemma lengthb_length: forall (l: list Tree) c t,
is_compact c -> 
c <= t ->
(tree l)  = (@rev_inj Tree_PPO RoseTree c )-> 
 lengthb (rforest t) = length l.
Proof.
intros l c t Hc Hle Heqc.
symmetry in Heqc.
cbn in Heqc.
rewrite (rev_inj_iff  _ _ _ Hc) in Heqc.
apply rforest_is_monotonic in Hle.
rewrite rforest_extends_forestb in Hle; auto.
rewrite <- Heqc in Hle.
rewrite rev_inj_inject in Hle.
cbn [forestb] in Hle.
inversion Hle; subst.
clear H2.
rewrite length_EXP2list in H1; auto.
Qed.

Lemma ppo_bot_rev_inj :
@ppo_bot Tree_PPO =
@rev_inj Tree_PPO RoseTree
  (@ppo_bot RoseTree).
Proof.
symmetry.
rewrite rev_inj_iff; auto; [| apply bot_is_compact].
now rewrite <- inject_bot.
Qed.  

Lemma compact_nth : forall (l : List RoseTree),
(forall n, n < lengthb l -> 
is_compact (P := RoseTree) (nthb n l)) ->
is_compact (rtree l).
Proof.
intros l Hall.
rewrite rtree_extends_treeb; [apply inject_compact|].
erewrite <- List2LIST2List with (d := ppo_bot).
apply LIST2List_compact.
remember (List2LIST ppo_bot l) as L.
destruct L.
- 
 apply summand_compact.
 assert (Heq' : LIST2List (sum_inj
  (fun n : nat =>
   EXP (BELOW n) RoseTree)
   j e) = (LIST2List (List2LIST ppo_bot l))) by now f_equal.
  rewrite List2LIST2List in Heq'.
  remember (sum_inj
      (fun n0 : nat =>
       EXP (BELOW n0) RoseTree)
      j e) as ee.
  destruct ee; try discriminate.
  injection Heqee ; intros; subst.
  apply inj_pair2 in H; subst.
  clear Heqee HeqL.
  rewrite compacts_are_functions_with_finite_support_and_compact_values.
  cbn in *.
  rewrite length_EXP2list in *.
  split.
   + 
     apply finite_type_all_sets_finite.
     apply BELOW_finite_type.
   +
     intros (x &Hx).
     specialize (Hall _ Hx).
     now rewrite nth_EXP2LIST with (Hi := Hx) in Hall.
-
 apply @bot_is_compact.
Qed. 
  

Lemma rle_le: forall t t', rle t t' -> t <= t'.
Proof.
intros t t' Hsle.
assert (Hd : is_directed ((compacts_le t))) by 
  now apply algebraic_dir.
assert (Hd' : is_directed ((compacts_le t'))) by 
  now apply algebraic_dir.
replace t with (cpo_lub (compacts_le t));
[|now rewrite algebraic_lub].
replace t' with (cpo_lub (compacts_le t'));
[|now rewrite algebraic_lub].
rewrite <- forallex_iff_lelub; auto ; [|now intros x (Hc & _)].
intros x (Hc & Hle).
replace t with (cpo_lub (compacts_le t)) in Hle;
   [|now rewrite algebraic_lub].
specialize Hc as Hc'.
specialize (Hc _ Hd Hle).
destruct Hc as (c & (Hc & Hlec) & Hlex).
replace c with 
(@inject Tree_PPO RoseTree (rev_inj c)) in Hlex;
[|now rewrite inject_rev_inj].
replace x with 
  (@inject Tree_PPO RoseTree (rev_inj x)) in Hlex;
  [|now rewrite inject_rev_inj].
rewrite <- inject_bimono in Hlex.
remember (rev_inj x) as x'.
remember (rev_inj c) as c'.
clear Hle Hd Hd'.
revert c x t t' Hsle Heqx' Heqc' Hlec Hc' Hc.
induction Hlex; intros  c x t t' Hsle Heqx' Heqc' Hlec Hc' Hc.
-
  exists ppo_bot.
  replace x with (@ppo_bot RoseTree).
  +
    repeat split; 
    [apply bot_is_compact | apply ppo_bot_least | apply poset_refl].
  +
    symmetry in Heqx'.
    rewrite rev_inj_iff in Heqx'; auto.
    rewrite <- Heqx'.
    now rewrite <- inject_bot.
-
 assert (Hex: forall n, n < length l ->
  exists y : RoseTree,
  member
     (compacts_le
        (nthb n  (rforest t'))) y /\
        (nthb n  (rforest x)) <= y).
  {
     intros n Hlt.
     apply  (H1 n Hlt 
       (nthb n (rforest c)) (nthb n (rforest x)) 
       (nthb n (rforest t)) (nthb n (rforest t'))).
     *
      apply rle_unfold in Hsle.
      destruct Hsle as 
      [Heq | (l1 & l'1 & Heq1 & Heq2 & Heql & Hall)];subst.
      - 
        rewrite le_bot_iff_eq in Hlec; subst.
        rewrite <- ppo_bot_rev_inj in Heqc'.
        discriminate.
      -
      specialize (lengthb_length _ _ _ Hc Hlec Heqc') as Heqlf.
      repeat rewrite rforest_rtree in *.
      apply Hall.
      cbn [lengthb] in *.
      lia.
      *
       rewrite rforest_extends_forestb ; auto.
       rewrite <- Heqx'.
       cbn [forestb].
       cbn.
       rewrite nth_EXP2LIST with (Hi := Hlt).
       rewrite rev_inj_inject.
       reflexivity.
      *
      rewrite rforest_extends_forestb ; auto.
      rewrite <- Heqc'.
      cbn [forestb].
      cbn.
      rewrite H in Hlt.
      rewrite nth_EXP2LIST with (Hi := Hlt).
      rewrite rev_inj_inject.
      reflexivity.
      *
       apply rforest_is_monotonic in Hlec.
       rewrite rforest_extends_forestb in Hlec; auto.
       rewrite <- Heqc' in Hlec.
       cbn [forestb] in Hlec.
       inversion Hlec; subst.
       rewrite length_EXP2list in *.
       cbn [nthb].
       rewrite H in Hlt.
       specialize (H5 _ Hlt).
       rewrite nth_EXP2LIST with (Hi := Hlt) in H5.
       cbn in H5.
       unfold list2EXP in H5.
       cbn in H5.
       eapply poset_trans; eauto.
       rewrite rforest_extends_forestb; auto.
       rewrite <- Heqc'.
       cbn [forestb].
       cbn.
       rewrite nth_EXP2LIST with (Hi := Hlt).
       rewrite <- inject_bimono.
       apply poset_refl.
      *  
      rewrite rforest_extends_forestb; auto.
      rewrite <- Heqx'.
      cbn.
      rewrite nth_EXP2LIST with (Hi := Hlt).
      apply inject_compact.
      *
      rewrite rforest_extends_forestb; auto.
      rewrite <- Heqc'.
      cbn.
      rewrite H in Hlt.
      rewrite nth_EXP2LIST with (Hi := Hlt).
      apply inject_compact.
      }   
  clear H1 H0.
  replace (length l) with (lengthb (rforest x)) in Hex;
  [|apply lengthb_length with (c:= x); auto; apply poset_refl].
  assert (Hex' : forall (ns : {n : nat| n < lengthb(rforest x)}),
  exists y : RoseTree,
        member
          (compacts_le
             (nthb (proj1_sig ns)
                (rforest t')))
          y /\
        nthb (proj1_sig ns) (rforest x) <=
        y
  ) by (intros (n & Hltn); now apply Hex).
  clear Hex.
  apply functional_choice in Hex'.
   assert (Hex : exists
  f : BELOW(lengthb
  (rforest x)) ->
      RoseTree, forall
    (j : BELOW(lengthb
    (rforest x))),
  member
    (compacts_le
       (nthb (nval  _ j)
          (rforest t')))
    (f j) /\
  nthb (nval _ j) (rforest x) <= f j).
  {
    destruct Hex' as (f & Hall).
    exists (fun n => f
     (exist _ (nval (lengthb (rforest x)) n) (is_below (lengthb (rforest x)) n))).
    intros j.
    destruct j ; subst.
    apply (Hall 
     (exist _ nval is_below)).
  }
  clear Hex'.
  destruct Hex as (f & Hall).
  specialize (lengthb_length l x x Hc' (poset_refl _) Heqx') as Hll.
  rewrite rle_unfold in Hsle.
  destruct Hsle as 
    [Heq | (l1 & l'1 & Heq1 & Heq2 & Heql & Hall')];subst.
  +
    rewrite le_bot_iff_eq in Hlec; subst.
    rewrite <- ppo_bot_rev_inj in Heqc'.
    discriminate.
  +
    exists (rtree (list_inj _ (EXP2list _ f) )).
    repeat split.
    *
    apply compact_nth.
    intros n Hlt.
    cbn [nthb lengthb] in *.
    rewrite length_EXP2list in Hlt.
    rewrite nth_EXP2LIST with (Hi := Hlt).
    apply Hall.
    *
    apply rtree_is_monotonic.
    constructor.
    {
      rewrite length_EXP2list; auto.
      repeat rewrite rforest_rtree in *.
      rewrite Hll.
      specialize (lengthb_length _ _ _ Hc Hlec Heqc') as Heqlf.
      repeat rewrite rforest_rtree in *.
      cbn [lengthb] in *.
      congruence.
    }
     intros i Hlt.
     rewrite length_EXP2list in Hlt; auto.
     rewrite nth_EXP2LIST with (Hi := Hlt).
     specialize (Hall {|
      nval := i;
      is_below := Hlt
    |}).
     destruct Hall as ((_ & Hm) & _ ).
     repeat rewrite rforest_rtree in *.
     apply Hm.
   *
   repeat rewrite rforest_rtree in *.
   cbn [nthb] in *.
   symmetry in Heqx'.
   rewrite rev_inj_iff in Heqx'; auto.
   rewrite <- Heqx' at 1.
   apply rforest_is_rev_monotonic.
   repeat rewrite rforest_rtree in *.
   rewrite rforest_extends_forestb; [|apply inject_compact].
   rewrite rev_inj_inject.
   cbn [forestb].
   constructor.
   --
    do 2 rewrite length_EXP2list; auto.
   --
     intros i Hlt.
     rewrite length_EXP2list in Hlt; auto.
     rewrite nth_EXP2LIST with (Hi := Hlt).
     unfold list2EXP.
     unshelve erewrite nth_EXP2LIST; [ now rewrite Hll|].
     specialize (Hall ({|
      nval := i;
      is_below := (eq_ind_r
      (fun n : nat => i < n)
      Hlt Hll)
     |})).
     destruct Hall as (_ & Hm).
     unfold list2EXP.
     cbn.
     eapply poset_trans; eauto.
     remember (rforest x) as f0.
     destruct f0.
     ++
      cbn.
      rewrite <- Heqx' in Heqf0.
      rewrite rforest_extends_forestb in Heqf0;
       [|apply inject_compact]. 
       rewrite rev_inj_inject in Heqf0.
       cbn [forestb] in *.
       cbn in Heqf0.
       injection Heqf0; intros; subst.
       rewrite nth_EXP2LIST with (Hi := Hlt).
       rewrite <- inject_bimono.
       apply poset_refl.
     ++ 
      rewrite <- Heqx' in Heqf0.
      rewrite rforest_extends_forestb in Heqf0;
       [|apply inject_compact].
       rewrite rev_inj_inject in Heqf0.
       discriminate.
 Qed.      
 
 

Lemma le_iff_rle: forall (t t' : RoseTree), 
t <= t' <-> rle t t'.
Proof.
split; intro Hle.
-
 now apply le_rle.
-
 now apply rle_le.
Qed.


Lemma rle_refl: forall (t : RoseTree), 
rle t t.
Proof.
intro t.
apply le_rle, poset_refl.
Qed.    

Lemma rle_trans: forall (t t' t'': RoseTree), 
rle t t' -> rle t' t'' -> rle t t''.
Proof.
intros t t' t'' Hle1 Hle2.
rewrite <- le_iff_rle in *.
eapply poset_trans; eauto.
Qed.


(*bisimulation*)
Inductive _bisim (R: RoseTree -> RoseTree -> Prop): 
RoseTree -> RoseTree -> Prop :=
|_bisim_bot : _bisim R ppo_bot ppo_bot
|_bisim_rtree :  forall (l l': list RoseTree), 
length l = length l' -> 
(forall n,
n < length l -> R (nth n l ppo_bot) (nth n l' ppo_bot)) -> 
_bisim R (rtree (list_inj _ l)) (rtree (list_inj _ l')).


Lemma _bisim_mono: 
  is_monotonic 
    (P1 := binary_poset) (P2 := binary_poset) 
  _bisim.
Proof.
intros R R' Hle x y Hsle.
inversion Hsle; subst.
-
  constructor.
-
   constructor; auto.
   intros n Hlt.
   now apply (Hle (nth n l ppo_bot) (nth n l' ppo_bot)), H0.
Qed.       

Definition bisim (t t': RoseTree) : Prop :=
gfp (L := binary_semilattice) _bisim _bisim_mono t t'.

Lemma bisim_unfold: forall (t t': RoseTree), 
 bisim t t' <-> 
((t = ppo_bot /\ t' = ppo_bot)\/ (exists (l l' : list RoseTree), length l = length l' /\
 t = rtree (list_inj _ l) 
/\ t' = rtree (list_inj _ l') /\
(forall n,
n < length l -> bisim (nth n l ppo_bot) (nth n l' ppo_bot)))).
Proof.
intros t t'.
specialize (@binary_unfold _ _ _ (_bisim_mono)) as Hfu.
assert (Hi : @gfp
(@binary_semilattice
   RoseTree
   RoseTree) _bisim
_bisim_mono  t t' <->
_bisim
(@gfp
   (@binary_semilattice
      RoseTree
      RoseTree)
   _bisim _bisim_mono) t t')
    by (now rewrite <- Hfu).
 split ; intro Hx.
 - 
  unfold bisim in Hx.
  rewrite Hi in Hx.
  replace (@gfp
  (@binary_semilattice
     RoseTree RoseTree)
  _bisim _bisim_mono) with bisim in Hx; auto.
  inversion Hx; subst.
  +
    now left.
  +
    right.
    now exists l,l'.
 -
   unfold bisim.
   rewrite Hi.
   replace (@gfp
  (@binary_semilattice
     RoseTree RoseTree)
  _bisim _bisim_mono) with bisim; auto.
  destruct Hx as [(Hb1 & Hb2) | (l & l' & Heq1 & Heq2& Heq3 & Heq4  )];
   subst; now constructor.
Qed.

Lemma bisim_coind: 
forall (R: binary RoseTree RoseTree),
(forall t t', 
 R t t' -> _bisim R t t') ->
(forall t t', R t t' -> bisim t t').
Proof.
intros S Hall.
apply binary_coind.
intros s Hm.
now apply Hall.
Qed.


Lemma bisim_refl: forall (t: RoseTree), bisim t t.
intro t.
remember t as t'.
rewrite Heqt' at 1.
revert t t' Heqt'.
apply bisim_coind.
intros t t' Heq; subst.
destruct (rose_tree_cases t) as [Heq | (a & Hneq & Heq)]; 
rewrite Heq; try constructor.
destruct a; try constructor; auto.
exfalso; now apply Hneq.
Qed.


Lemma bisim_sym: forall (t t': RoseTree), 
bisim t' t -> bisim t t'.
apply bisim_coind.
intros s s' Heq; subst.
rewrite bisim_unfold in Heq.
destruct Heq as [(Hb1 & Hb2) | (l & l' & Heq1 & Heq2 & Heq3 & Ha)]; 
  subst; try constructor; auto.
intros n Hlt.
rewrite <- Heq1 in Hlt.
now apply Ha.
Qed.


Lemma bisim_rle: forall (t t' : RoseTree), 
bisim t t' -> rle t t'.
Proof.
apply rle_coind.
intros s s' Hb.
rewrite bisim_unfold in Hb.
destruct Hb as [(Hb1 & Hb2) | (l & l' & Heq1 & Heq2 & Heq3 & Ha)]; 
  subst; now constructor.
Qed.


Lemma bisim_rle': forall (t t' : RoseTree), 
bisim t t' -> rle t' t.
Proof.
intros t t' Hb.
apply bisim_sym in Hb.
now apply bisim_rle.
Qed.


Lemma rle_bisim: forall (t t' : RoseTree), 
rle t t' -> rle t' t -> bisim t t'.
Proof.
intros t t' Hle1 Hle2.
apply rle_le in Hle1, Hle2.
assert (Heq : t = t') by (now apply poset_antisym); subst.
apply bisim_refl.
Qed.

Lemma bisim_eq: forall (t t' : RoseTree),
bisim t t' -> t = t'.
intros t t' Hb.
apply poset_antisym.
-
 now apply rle_le, bisim_rle.
-
 now apply rle_le, bisim_rle'.
Qed.

Lemma eq_bisim: forall (t t' : RoseTree),
t = t' -> bisim t t'.
Proof.
intros t t' Heq ; subst.
apply bisim_refl.
Qed.

Lemma bisim_iff_eq : forall (t t' : RoseTree),
t = t' <-> bisim t t'.
Proof.
split; intro Heq.
- now apply eq_bisim.
- now apply bisim_eq.
Qed.



Lemma rle_antisym : forall (t t' : RoseTree),
rle t t' -> rle t' t -> t = t'.
Proof.
intros t t' Hb1 Hb2.
rewrite bisim_iff_eq.
now apply rle_bisim.
Qed.


Lemma bisim_trans: forall (t t' t'' : RoseTree),
bisim t t' -> bisim t' t'' -> bisim t t''.
Proof.
intros t t' t'' Hb1 Hb2.
rewrite <- bisim_iff_eq in *; now subst.
Qed.


  

