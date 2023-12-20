From Coq Require Import FunctionalExtensionality
  PropExtensionality IndefiniteDescription Logic.Eqdep Classical.
From Corec Require Export Completion.


Inductive SUM{J:Type}(T : J -> Type) : Type :=
| sum_inj : forall j, T j -> SUM  T
| sum_bot : SUM T.


Inductive sum_le{J: Type}{T : J -> Poset}: SUM T -> SUM T -> Prop :=
|sum_le_bot : forall x,  sum_le  (sum_bot  T) x
|sum_le_inj : forall j (p1 p2 : T j),
    p1 <= p2 -> sum_le (sum_inj _ j p1) (sum_inj _ j p2).


Lemma sum_le_bot_least{J: Type}{T : J -> PPO}: forall (x:SUM T),
    sum_le (sum_bot T) x.
Proof.
intros x; destruct x;constructor.
Qed.
  
Lemma sum_le_refl{J: Type}{T : J -> Poset}: forall (x: SUM T),
    sum_le x x.
Proof.
intro x.
destruct x; constructor.
apply poset_refl.
Qed.

Lemma sum_le_trans{J: Type}{T : J -> Poset}: forall (x y z: SUM T),
    sum_le x y -> sum_le y z -> sum_le x z.
Proof.  
intros x y z Hle1 Hle2.
inversion Hle1; subst; inversion Hle2; subst; try constructor.
apply inj_pair2 in H2; subst.
eapply poset_trans; eauto.
Qed.

Lemma sum_le_antisym{J:Type}{T : J -> Poset}:
  forall (x y: SUM T),
    sum_le x y -> sum_le y x -> x = y.
Proof.
intros x y Hle1 Hle2.
inversion Hle1; subst; inversion Hle2; auto;  subst.
apply inj_pair2 in H2, H3; subst.
f_equal.
now apply poset_antisym.
Qed.


Definition SUM_Poset{J: Type}(T : J -> Poset) : Poset :=
{|
  poset_carrier := SUM T;
  poset_le := sum_le;
  poset_refl := sum_le_refl;
  poset_trans := sum_le_trans;
  poset_antisym := sum_le_antisym
|}.


Definition SUM_PPO{J: Type}(T : J -> PPO) : PPO :=
{|
  ppo_poset := SUM_Poset T;
  ppo_bot := sum_bot T;
  ppo_bot_least := sum_le_bot_least;
|}.


Lemma sum_inj_rev_mono{J:Type} :
   forall (T : J -> PPO) (j : J),
     is_rev_monotonic (P1 := T j) (P2:= SUM_PPO T)
       (sum_inj T j).
Proof.  
intros T j  x y Hle.
inversion Hle; intros ;subst.
now apply inj_pair2 in H1, H2; subst.
Qed.


Lemma sum_inj_bimono{J:Type} :
   forall (T : J -> PPO) (j : J),
     is_bimonotonic (P1 := T j) (P2:= SUM_PPO T)
       (sum_inj T j).
Proof.
intros T j.
split; intros x y Hle.
- 
  now constructor.
-
  now apply sum_inj_rev_mono.
Qed.


Lemma member_sum_same_idx{J : Type} :
  forall (T: J -> PPO) (S : Setof (SUM_PPO T)) j j' p p',
  is_directed S ->  
  member S (sum_inj _ j p) ->
  member S (sum_inj _ j' p') ->  j = j'.
Proof.
intros T S j j' p p' Hd Hm Hm'.
cbn in *.
destruct Hd as (_ & Hd).
specialize (Hd _ _ Hm Hm').
destruct Hd as (z & Hmz & Hle1 & Hle2).
inversion Hle1; inversion Hle2; subst.
apply inj_pair2 in H1,H5; subst.
injection H4; clear H4; intros H4 Heq; now subst.
Qed.

Lemma is_directed_in_sum{J : Type}:
  forall (T : J -> CPO) (S : Setof (SUM T)),
    is_directed  (P := SUM_PPO T) S ->
    S = single (sum_bot T) \/
      exists j Sj,  remove S (sum_bot T)  =
                      fmap Sj (sum_inj _ j) /\
                      is_directed Sj.
Proof. 
intros T S Hd.
destruct (oracle ( S = single (sum_bot T) )); [now left |].
right.
remember Hd as Hd'.
destruct Hd' as (Hne & Ha).
apply not_empty_not_single_2dif in n; auto.
destruct n as (y & Hmy & Hney).
destruct y; [| exfalso; now apply Hney].
clear Hney HeqHd'.
exists j.
remember (fun p => member S (sum_inj _ j p)) as Sj.
assert (Heq : remove S (sum_bot (fun x : J => T x)) =
  fmap Sj (sum_inj (fun x : J => T x) j)).
{
apply set_equal; intro x ; split; intro Hm.
-
  destruct Hm as (Hm & Hnex).
  destruct x; [| exfalso; now apply Hnex].
  clear Hnex.
  specialize
    (member_sum_same_idx _ _ _ _ _ _
       Hd Hmy Hm) as Heq; subst.
  exists p0; split; auto.
-
  destruct Hm as (p' & Hmp' & Heqp');subst.
  split; [auto | intro ; discriminate].
}  
exists Sj.
split; [apply Heq |].
apply
  (@rev_monotonic_directed
     (T j)
     (SUM_PPO T) Sj (sum_inj T j)).
- 
  intros x y Hle.
  inversion Hle ; subst.
  apply inj_pair2 in H1, H2; now subst.
-
  cbn in *.
  rewrite <- Heq.
  eapply
    (@remove_bot_directed  (SUM_PPO T));
    eauto.
  intro; discriminate.
Qed.

Lemma in_sum_is_directed{J : Type}:
  forall (T : J -> CPO)
         (j : J) (Sj : Setof (T j)),
    is_directed Sj -> is_directed  (P := SUM_PPO T)
                        (fmap Sj (sum_inj _ j)).
Proof. 
intros T j Sj Hd.
apply @monotonic_directed; auto.
intros x y Hle.
now constructor.
Qed.



Lemma is_directed_in_sum_iff{J : Type}:
  forall (T : J -> CPO) (S : Setof (SUM T)),
    is_directed  (P := SUM_PPO T) S <->
    S = single (sum_bot T) \/
      (S <>  single (sum_bot T) /\
         exists j Sj,  remove S (sum_bot T)  =
                      fmap Sj (sum_inj _ j) /\
                      is_directed Sj).
Proof.
split.
-   
  intro Hd.
  destruct (oracle (S = single   (sum_bot (fun x : J => T x))));
    [subst; now left | right; split; auto].
   destruct (is_directed_in_sum _ _ Hd); [exfalso; now apply n | auto].
-
  intro Hd.
  destruct (oracle (S = single   (sum_bot (fun x : J => T x))));
    [subst; apply @single_is_directed | ].  
  destruct Hd as [Heq | (_ & Hd) ]; [subst; exfalso ; now apply n |].
  destruct Hd as (j & Sj & Heq & Hd).
  destruct (oracle (member S (sum_bot T))).
  +
    replace S with (add (remove S (sum_bot T)) (sum_bot T)).
    * 
      apply @is_directed_add_ppo_bot.
      rewrite Heq.
      now apply in_sum_is_directed.
    *  
      now rewrite add_remove_eq.
  +
    rewrite not_member_remove_eq in Heq; auto.
    rewrite Heq.
    now apply in_sum_is_directed.
Qed.


Lemma is_lub_sum_inj{J : Type}:
  forall (T : J -> CPO)
         (j : J) (Sj : Setof (T j)) lj,
 ~is_empty Sj ->
  is_lub Sj lj ->
   is_lub (P := SUM_PPO T) (fmap Sj (sum_inj _ j))
    (sum_inj _ j
       lj).
Proof.
intros T j Sj l  Hne Hl.
destruct (oracle (Sj =single (@ppo_bot (T j)))).
{
  subst.
  rewrite (fmap_single).
  assert (l =ppo_bot).
  {
    apply le_bot_eq.
    destruct Hl as (_ & Hmin).
    apply Hmin.
    intros x Hm.
    rewrite member_single_iff in Hm.
    subst; apply poset_refl.
  }  
  subst.
  split.
  - intros x Hm.
    destruct Hm.
    apply poset_refl.
  -
    intros y Hu'.
    unfold is_upper in Hu'.
    apply Hu'.
    apply member_single.    
}  
split.
- 
  intros y Hm.
  apply inv_member_fmap in Hm.
  destruct Hm as (x & Heq & Hm); subst.
  constructor.
  destruct Hl as (Hu & _).
  now apply (Hu x).
-
  intros y Huy.
  destruct y.
  {
  destruct Hl as (Hu & Hmin).
  destruct (not_empty_not_single_2dif  _ _ Hne n)
    as (x & Hmx & Hnb).
  specialize (@member_fmap _ _ Sj (sum_inj T j) _ Hmx) as Hmf.
  specialize Huy as Huy'.
  specialize (Huy _ Hmf).
  clear Hmf.
  inversion Huy; subst.
  apply inj_pair2 in H1, H3; subst.
  inversion Huy; subst; clear Huy.
  apply inj_pair2 in H2, H3; subst.
  constructor.
  clear H0.
  apply Hmin.
  intros u Hmu.
  specialize (@member_fmap _ _ Sj (sum_inj T j0) _ Hmu) as Hpmu.
  specialize (Huy' _ Hpmu).
  inversion Huy'.
  apply inj_pair2 in H2, H3 ; now subst.
  }
  { 
    exfalso.
    destruct (not_empty_not_single_2dif  _ _ Hne n)
      as (x & Hmx& Hneb).
    specialize (@member_fmap _ _ Sj (sum_inj T j) _ Hmx) as Hmf.
    specialize (Huy _ Hmf).
    inversion Huy.
   }
Qed.


Lemma is_directed_lub{J : Type}:
  forall (T : J -> CPO) (S : Setof (SUM T)),
    is_directed  (P := SUM_PPO T) S ->
    {x : SUM T  | is_lub (P := SUM_PPO  T) S x}.
Proof.  
intros T S Hd.
specialize Hd as Hd'.  
rewrite is_directed_in_sum_iff in Hd.
apply constructive_indefinite_description.
destruct Hd as [Heq | (Hne & Hex)]; subst.
-
  exists (sum_bot T).
  subst.
  apply @is_lub_single.
-  
  destruct Hex as (j & Sj & Heq & Hd).
  exists (sum_inj _ j (cpo_lub Sj)).
  remember (cpo_lub Sj) as lj.
  assert (Hil : is_lub Sj lj); [subst; apply cpo_lub_prop; auto | ].
  destruct Hd' as (Hnem & _).
  destruct Hd as (Hned & Hx).
  destruct (oracle (Sj = single ppo_bot)).
  {
    rewrite Heqlj.
    subst.
    rewrite cpo_lub_single.
    rewrite fmap_single in Heq.
    apply @remove_is_single in Heq.
    cbn in Heq.
    destruct Heq as [Heq1 | Heq2]; subst.
    -
      specialize (ordered_pair_has_lub (P := SUM_PPO T) (sum_bot T)  (sum_inj
              (fun x : J => T x) j ppo_bot)) as Hopl.
      cbn in *.
      rewrite ordered_pair_reorder.
      apply Hopl.
      constructor.
    - 
      apply (is_lub_single (P := SUM_PPO T)).
  }  
  specialize (@is_lub_sum_inj J T j Sj lj Hned) as Hlui.  
  cbn in Hlui.
  rewrite <-Heq in Hlui.
  cbn in Hlui.
  rewrite <- (@is_lub_remove_bot (SUM_PPO T)) in Hlui; auto.
Qed.
    


Program
Definition SUM_CPO{J: Type}(T : J -> CPO) : CPO :=
{|
  cpo_ppo := SUM_PPO T;
  cpo_lub := fun S => match (oracle (is_directed S))
    with
      left Hd =>  proj1_sig (is_directed_lub  _ S Hd)
    | right _ => sum_bot (fun x : J => T x)
    end;
    cpo_lub_prop := fun S Hd =>  _
     (*match (oracle (is_directed S)) with
     left _ => _
     | right _ => _
     end*)
      
|}.

Next Obligation.
cbn.
intros.
destruct ( oracle (is_directed (P := SUM_Poset T)S) ); [|contradiction].
apply ((proj2_sig (is_directed_lub T S i))).
Qed.




Lemma compact_summand{J:Type}(T : J -> CPO):
  forall (x : SUM_CPO T),
is_compact (P := SUM_CPO T) x ->
x = sum_bot T \/
             exists j (p: T j), x = sum_inj T j p /\ is_compact p.
Proof.
intros x Hc.
destruct (oracle (x = sum_bot T)); [now left |].
right.
destruct x; [clear n| exfalso; now apply n].
exists j; exists p; split; auto.
intros Sj Hdj Hlej.
remember (fmap Sj (sum_inj T j)) as S.
assert (Hd : is_directed (P:= SUM_PPO T) S).
{
rewrite is_directed_in_sum_iff.
right.
split.
-  
  subst.
  intro Habs.
  assert (Heq : member (fmap Sj (sum_inj (fun x : J => T x) j)) (sum_bot T))
    by (rewrite Habs;apply member_single).
  destruct Heq as (u & Hu & Hd); discriminate.
-
  exists j ; exists Sj.
  split; auto.
  replace (remove S (sum_bot (fun x : J => T x))) with S; auto.
  symmetry.
  rewrite not_member_remove_eq; auto.
  intro Hm.
  subst.
  destruct Hm as (u & Hu & Hd); discriminate.
}  
assert (Hle :poset_le (p :=SUM_PPO T)
               (sum_inj _ j p)
               (sum_inj _ j (cpo_lub Sj)))
  by (now constructor).
destruct (oracle (Sj = single  ppo_bot)).
{
  subst; exists ppo_bot.
  rewrite cpo_lub_single in Hlej.
  split; auto.
  apply member_single.
}  
assert(Hil :is_lub (P := SUM_PPO T) S (sum_inj _ j (cpo_lub Sj))).
{
subst.
specialize Hdj as Hdj';
destruct Hdj' as (Hnej & _).
apply is_lub_sum_inj; auto.
now apply cpo_lub_prop.
}
assert (Heq : (sum_inj _ j (cpo_lub Sj)) = cpo_lub (c := SUM_CPO T) S).
{
  specialize (cpo_lub_prop (c:= SUM_CPO T) _ Hd) as Hcp.
  apply  (is_lub_unique (P:=SUM_PPO T) S);auto.
}
cbn in Hle.
rewrite Heq in Hle.
specialize (Hc _ Hd Hle).
destruct Hc as (c & Hmc & Hlec).
destruct c; [| apply @le_bot_eq in Hlec;  discriminate].
inversion Hlec; subst.
apply inj_pair2 in H1,H3; subst.
inversion Hlec.
apply inj_pair2 in H2,H3; subst.
exists p0; split; auto.
destruct Hmc as (p' & Hmp' & Heqp').
injection Heqp' ; intros; subst.
apply inj_pair2 in H; subst; auto.
Qed.



Lemma fmap_lub_is_lub_from_lub_of_summand{J:Type}:
  forall (T : J -> PPO) (j : J)
         (Sj : Setof (T j)) (l : SUM T),
    ~is_empty Sj -> 
     is_lub (P := SUM_PPO T)(fmap Sj (sum_inj _ j)) l ->
    exists lj : T j, l = sum_inj _ j lj /\ is_lub Sj lj.
Proof.
intros T j Sj l Hne Hl.
remember Hl as Hl'.
clear HeqHl'.
destruct Hl' as  (Hu & _).
  
assert (Hnej : ~ is_empty  (fmap Sj (sum_inj T j)))
  by (now apply not_empty_fmap).
destruct l.
{
  rewrite not_empty_member in Hne.
  destruct Hne as (p' & Hmp').
  apply member_fmap with (f := sum_inj T j) in Hmp'.
  specialize (Hu _ Hmp').
  inversion Hu ; intros ; subst.
  apply inj_pair2 in H1, H3; subst.
  rename j0 into j.
  clear p' H0 Hu Hmp'.
  exists p; split; auto.
  
  eapply (is_lub_fmap_rev (P2 := SUM_PPO T)) with (f := sum_inj T j); eauto.
  apply sum_inj_bimono.
}  
{
  apply (@lub_bot_implies_single_bot (SUM_PPO T)) in Hu ;
  auto.
  cbn.
  exfalso.
  assert
    (Hm : member(fmap Sj (sum_inj _ j ))  (sum_bot T))
    by (rewrite Hu; apply member_single).
  destruct Hm as (y & Hy & Heq);discriminate.
  }  
Qed.


Lemma summand_compact{J:Type}(T : J -> CPO):
  forall (j:J) (p : T j),
    is_compact p -> is_compact (P := SUM_CPO T) (sum_inj _ j p).
Proof.
intros j p Hcj S Hd Hle.
specialize Hd as HS.  
specialize (is_directed_in_sum_iff _ S) as Heqv.
cbn in HS. (*  do not remove even -  effect under the hood*)
rewrite Heqv in HS.
clear Heqv.
destruct HS as [Hb | Hex].
{
subst.
exists (sum_bot T); split; [apply member_single |].
now rewrite  @cpo_lub_single in Hle.
}
destruct Hex as (Hnes & j' & Sj & Heq & Hmj).
specialize (cpo_lub_prop S Hd) as Hil.
specialize Hd as Hd'.
destruct Hd' as (Hne & _).
rewrite is_lub_remove_bot in Hil; auto.
cbn in Hil.

destruct (oracle (is_directed (P := SUM_Poset T)S));
[ | contradiction]. 
rewrite Heq in Hil.
remember  (proj1_sig (is_directed_lub T S Hd)) as l.
remember Hmj as Hdj.
destruct Hdj as (Hnej & X).
clear HeqHdj X.
specialize
  (fmap_lub_is_lub_from_lub_of_summand
     _ _ Sj _ Hnej Hil) as Hex.
cbn in Hex.
destruct Hex as (lj & Heq' & Hlub).
assert (i = Hd) by
  apply proof_irrelevance.
rewrite H in *; clear H.  



(* preparing proof of  j = j'
 *)

rewrite <- Heq in Hil.
rewrite <- (is_lub_remove_bot _ _ Hne) in Hil; auto.
specialize (cpo_lub_prop S Hd) as Hlil.
cbn in Hil, Heql.


rewrite <- Heql in Hil.
apply is_lub_unique with (x :=l) in Hlil ; auto.
rewrite <- Hlil, Heql in Hle.
cbn in Hle.
rewrite  Heq' in Hle.
inversion Hle; intros; subst.
apply inj_pair2  in H1,H3; subst.
(* done priving j = j' *)
rename j' into j, H0 into Hlej.
remember (proj1_sig (is_directed_lub T S Hd)) as l.
(* preparing to use the fact that p is compact *)
specialize (cpo_lub_prop Sj Hmj) as  Hlbj.
eapply is_lub_unique   with (x :=lj) in Hlbj ;auto.
rewrite Hlbj in Hlej.
(* using compactness of p *)
specialize (Hcj _ Hmj Hlej).
destruct Hcj as (cj & Hmcj & Hlecj).
exists (sum_inj _ j cj).
split ; [| now constructor].
apply (member_fmap Sj (sum_inj T j)) in Hmcj.
cbn in Hmcj.
rewrite <- Heq in Hmcj.
now destruct Hmcj as (Hmcj & _).
Qed.


Lemma compacts_le_bot{J:Type}:
  forall (T : J -> CPO),
compacts_le (P:= SUM_CPO T) (sum_bot T) = single (sum_bot T).
Proof.
intros T.
apply set_equal; intro x; split; intro Hm.
- 
  destruct Hm as (Hc & Hleb).
  apply @le_bot_eq in Hleb; subst.
  apply member_single.  
-
  rewrite  member_single_iff in Hm; subst.
  split; [apply @bot_is_compact | apply poset_refl].
Qed.


Lemma my_algebraic_dir{J : Type}:
  forall (T : J -> ALGEBRAIC)
    (c : SUM_CPO T),
    is_directed (compacts_le c).
Proof.
intros T c.
split; [apply nonempty_compacts_le |].
intros x y (Hcx & Hlex) (Hcy & Hley).
specialize Hcx as Hcx'.
specialize Hcy as Hcy'.
apply compact_summand in Hcx',Hcy'.
destruct Hcx' as [He | Hexx]; 
  [exists y; subst; repeat split; auto;
    [apply @ppo_bot_least | apply poset_refl]|].
destruct Hcy' as [He | Hexy]; 
  [exists x; subst; repeat split; auto;
          [apply  poset_refl  | apply @ppo_bot_least]|].
destruct Hexx as (j & p & Heq & Hcp);subst.
destruct Hexy as (j' & p' & Heq & Hcp');subst.
inversion Hlex; subst.
apply inj_pair2 in H1; subst.
inversion Hley; subst.
apply inj_pair2 in H1,H4; subst.
clear p4 H0.
inversion Hley; subst.
apply inj_pair2 in H1,H3; subst.
clear Hlex Hley Hcx Hcy.
specialize (@algebraic_dir (T j)); intro Had.
specialize (Had p2).
destruct Had as (_ & Had).
specialize (Had p p' (ltac:(split;auto)) (ltac:(split;auto))).
destruct Had as (z & (Hcz & Hlez) & Hle1 & Hle2).
cbn.
exists (sum_inj _ j z).
repeat split; auto; try constructor; auto.
now apply summand_compact.
Qed.


Lemma compacts_le_are{J : Type}:
  forall (T : J -> ALGEBRAIC)
  (c : SUM_CPO T),
compacts_le c = single (sum_bot T) \/
              exists j cj,
                c = sum_inj _ j cj /\
                  (remove (compacts_le c) (sum_bot T)) =
                    fmap ( compacts_le cj) (sum_inj _ j).
Proof.
intros T c.
destruct c; [right|left; apply compacts_le_bot].
exists j, p; split; auto.
apply set_equal; intro x; split; intro Hm.
- 
  destruct Hm as ((Hc & Hle) & Hnb).
  destruct x; [clear Hnb|exfalso; now apply Hnb].
  inversion Hle; subst.
  apply inj_pair2 in H1,H3; subst.
  clear H0 p4.  
  exists p0; split; auto.
  split; [|inversion Hle; subst;  apply inj_pair2 in H1,H2; now subst].
  apply compact_summand in Hc.
  destruct Hc as [Habs | Hex]; [discriminate|].
  destruct Hex as (j' & p' & Heq & Hc).
  injection Heq; intros ; subst.
  apply inj_pair2 in H; now subst.
-
  destruct Hm as (p' & (Hc & Hle) & Heq).
  split ; [| subst;  intro Habs; discriminate].
  subst.
  split; [| now constructor ].
  now apply summand_compact.
Qed.


Lemma my_algebraic_lub_aux {J : Type} :
    forall (T : J -> ALGEBRAIC)
    (c : SUM_CPO (fun x : J => T x)),
      compacts_le c = single (sum_bot (fun x : J => T x)) ->
      is_lub (compacts_le c) c.
Proof.
intros T c Heq.  
destruct c.
-
  exfalso.
  assert (Hm :
             member (@compacts_le (SUM_CPO T)
                       (sum_inj T j p))
               (sum_inj T j (@ppo_bot (T j)))).
  {
    split; try constructor; try apply ppo_bot_least.
    apply summand_compact.
    apply bot_is_compact.
  }
  rewrite Heq in Hm.
  rewrite member_single_iff in Hm.
  discriminate.
-
  rewrite Heq.
  apply @is_lub_single.
Qed.
  
Lemma my_algebraic_lub{J : Type} :
  forall (T : J -> ALGEBRAIC)
    (c : SUM_CPO (fun x : J => T x)),
  c = cpo_lub (compacts_le c).
Proof.
intros T c.
apply is_lub_cpo_lub_eq; [| apply my_algebraic_dir].
specialize  (@nonempty_compacts_le _ c) as Hne.
destruct ( oracle (compacts_le c =
          single
            (sum_bot T))); [ now apply my_algebraic_lub_aux |].
destruct (compacts_le_are T c) as [Hnbot | Hbot];
[exfalso ; now apply n|].
destruct Hbot as (j & cj & Heqcj & HeqS).
rewrite @is_lub_remove_bot; auto.
cbn in *.
rewrite HeqS; clear HeqS.
subst.
specialize (@algebraic_lub (T j)cj ) as Hal.
specialize (@cpo_lub_prop
                  _ (compacts_le cj)
                  (@algebraic_dir _ cj) ) as Hclp.
rewrite <- Hal in Hclp.  
specialize (is_lub_sum_inj T j (compacts_le cj)) as Hil.
cbn in Hil.
specialize  (@nonempty_compacts_le (T j) cj) as Hnej.
cbn in Hnej.
specialize (Hil cj Hnej).
now apply Hil.

Qed.




Definition SUM_ALGEBRAIC{J : Type}(T: J -> ALGEBRAIC): ALGEBRAIC :=
  {|
    algebraic_cpo := SUM_CPO T;
    algebraic_dir := my_algebraic_dir T;
    algebraic_lub := my_algebraic_lub T
  |}.


Lemma compact_nonbot_summand{J:Type}(T : J -> CPO):
  forall j p,
  is_compact (P := SUM_CPO T) (sum_inj T j p) ->
  is_compact p.
Proof. 
intros j p Hc.
apply compact_summand in Hc.
destruct Hc as [Hdisc | Hex]; [discriminate |].
destruct Hex as (j' & p' & Heq & Hc).
injection Heq; intros; subst.
apply inj_pair2 in H; now subst.
Qed.

Program Definition
  sum_completion{J : Type}(P : J -> PPO) (T: forall j, COMPLETION (P j))
  : COMPLETION (SUM_PPO P) :=
{|
  alg := SUM_ALGEBRAIC T;
  
  inject :=
   fun (x : SUM_PPO P) =>
    match x with
    | sum_inj _ j t => sum_inj _ j (@inject (P j) (T j) t)
    | sum_bot _ => sum_bot _
    end;
  
  rev_inj :=
    fun (cc : SUM_ALGEBRAIC T)  =>
    match (oracle (is_compact cc)) with
    left _ =>
      match cc  with
      | sum_inj _ j t =>  sum_inj _  j (@rev_inj (P j) (T j) t)
      | sum_bot _ => sum_bot _
   end
   | right _ => sum_bot _
  end
|}. 

Next Obligation.
cbn.
intros.
reflexivity.
Qed.  

Next Obligation.
cbn.  
intros.
split; intros Hle.
-
  inversion Hle; subst.
  +
    constructor.
  +
    constructor.
    now rewrite <- inject_bimono.
-
  inversion Hle; subst.
  +
    destruct p; try discriminate.
    constructor.
  +
    cbn in *.
    destruct p; try discriminate; try constructor.
    injection H; intros ; subst.
    apply inj_pair2 in H2; subst.
    destruct p'; try discriminate; try constructor.
    injection H0; intros; subst.
    apply inj_pair2 in H2; subst.
    constructor.
    now rewrite <- inject_bimono  in *.
Qed.

Next Obligation.
cbn.  
intros.
destruct p.
- 
  apply summand_compact.
  apply inject_compact.
-
  apply @bot_is_compact.
Qed.

Next Obligation.
cbn.
intros J P T cc p Hc.
destruct (oracle (is_compact (P := SUM_CPO T) cc)) as [Hc'  | n];
 [| exfalso; now apply n].
 destruct cc; destruct p; try tauto; 
 try (split;intro Heq; discriminate).
 split;intro Heq.
 -
   injection Heq; intros; subst.
   apply inj_pair2 in H; subst.
   f_equal.
   rewrite <- rev_inj_iff; auto.
   now apply compact_nonbot_summand in Hc.
-
 injection Heq; intros; subst.
 apply inj_pair2 in H; subst.
 f_equal.
 rewrite  rev_inj_iff; auto.
 now apply compact_nonbot_summand in Hc.
Qed.
