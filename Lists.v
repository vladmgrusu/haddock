From Coq Require Import FunctionalExtensionality ProofIrrelevance 
 List Lia Eqdep IndefiniteDescription.
Import ListNotations Nat.
From Corec Require Export Sum Exp.


Definition LIST(T:Type) : Type :=
SUM (fun n => EXP (BELOW n) T).


Definition LIST_Poset(P:Poset) : Poset :=
SUM_Poset (fun n => EXP_Poset (BELOW n) P).

Definition LIST_PPO(P:PPO) : PPO :=
SUM_PPO (fun n => EXP_PPO (BELOW n) P).

Definition LIST_bot(P:PPO) := 
   sum_bot (fun x : nat => BELOW x -> P).

Definition LIST_CPO(C:CPO) : CPO :=
SUM_CPO (fun n => EXP_CPO (BELOW n) C).


Definition LIST_ALGEBRAIC(A:ALGEBRAIC) : ALGEBRAIC :=
SUM_ALGEBRAIC (fun n => EXP_BELOW_ALGEBRAIC n A).


Definition LIST_completion(P:PPO)(T:COMPLETION P):COMPLETION (LIST_PPO P) :=
sum_completion (fun n => EXP_PPO (BELOW n) _) (fun n => exp_below_completion n _ T).


Definition list2EXP{T:Type}(d:T) (N: nat)(l : list T):  
  EXP (BELOW N) T := (fun i => nth i l d).
 
Program Definition EXP2list{T:Type}(N: nat) (e :EXP (BELOW N) T) : 
  list T :=
match N with
| 0 =>  []
|  S N' =>  bEXP2list N' e
end .

Next Obligation.
intros.
exact Heq_N.
Defined.

Lemma length_EXP2list{T:Type}: forall N (e: EXP (BELOW N) T),
 length (EXP2list N e) = N.
Proof.
destruct N; intro e; auto.
apply blength_EXP2list.
Qed.


Lemma nth_EXP2LIST{T:Type}(d:T): 
forall N (e: EXP (BELOW N) T) (i: nat) (Hi : (i < N)%nat), 
  nth i (EXP2list N e) d = e {| nval:= i; is_below := Hi |}. 
Proof.
destruct N ; intros; try lia.
cbn.
now rewrite bnth_EXP2list with (Hi := Hi).
Qed.


Lemma EXP2list2EXP{T:Type}: forall (d:T) n e,  (
  list2EXP d n (EXP2list n e)) = e.
Proof.
intros d n e.
extensionality x.
unfold list2EXP.
unshelve erewrite nth_EXP2LIST.
+
  now destruct x.
+
  do 2 f_equal.
Qed.



Lemma blist2EXP2list{T:Type}: 
forall (d:T) N l, length l =   S N -> bEXP2list N (list2EXP d (S N) l) = l.
Proof.
intro d.
induction N; intros l Heq.
-
  destruct l; cbn in Heq ; try lia.
  destruct l; cbn in Heq ; try lia.
  reflexivity.
-
  destruct l; cbn in Heq; try lia.
  apply eq_add_S in Heq.
  specialize (IHN _ Heq).
  cbn in *.
  f_equal.
  replace (list2EXP d (S N) l) with
  (bshift N
     (fun x : BELOW (S (S N)) =>
      match nval (S (S N)) x with
      | 0 => t
      | S m => nth m l d
      end)); auto.
 Qed. 


Lemma list2EXP2list{T:Type}: 
  forall (d:T) N l, length l = N -> EXP2list N (list2EXP d N l) = l.
Proof.
intros d N l Heq.
destruct N.
-
  destruct l ;cbn in Heq; try lia.
  reflexivity.
-   
  cbn.
  now apply blist2EXP2list.
Qed.  


Inductive List(T:Type) : Type :=
|list_inj : list T -> List T
|list_bot : List T.

Definition List2LIST{T:Type}(d:T)(l : List T) : LIST T :=
match l with
  | list_inj  _ l' =>  
     sum_inj _ (length l')  (list2EXP d  (length l') l')
  | list_bot _ => sum_bot _
end.

Definition LIST2List{T:Type}(L:LIST T) : List T :=
match L with
|  sum_inj  _ j x => 
    list_inj _  (EXP2list j x)
| sum_bot _ => list_bot _
end.

Lemma List2LIST2List{T:Type} (d:T): forall (l : List T),
        LIST2List(List2LIST d l) = l.
Proof.
intro l.
destruct l ; auto.
cbn.
f_equal.
rewrite list2EXP2list; auto.
Qed.

Lemma LIST2List2LIST{T:Type} (d:T): forall (L : LIST T),
        List2LIST d (LIST2List L) = L.
Proof.        
intro L.
destruct L ; auto.
cbn.
f_equal.
rewrite length_EXP2list.
now rewrite EXP2list2EXP.
Qed.


Inductive List_le{P: PPO} : List P -> List P -> Prop :=
|List_le_bot : forall l, List_le (list_bot P) l  
|List_le_list : forall l1 l2, length l1 = length l2 ->
(forall i, (i < length l1)%nat -> 
 (nth i l1 ppo_bot) <=(nth i l2 ppo_bot)) 
-> List_le (list_inj _ l1) (list_inj  _ l2).

Lemma List_le_refl{P:PPO} : forall (l : List P), List_le l l.
Proof.
induction l.
- constructor; auto.
  intros; apply poset_refl.
-  
  constructor.
Qed.

Lemma List_le_trans{P:PPO} : forall (l1 l2 l3:List P),
List_le l1 l2 -> List_le  l2 l3 -> List_le l1 l3.
Proof.
intros l1 l2 l3  Hl1l2.
revert l3.
induction Hl1l2; intros l3 Hl2l3.
-
  constructor.
-
  inversion Hl2l3; subst.
  constructor.
  +
    congruence.
  +
    intros i Hlt.
    specialize (H0 _ Hlt).
    rewrite H in Hlt.
    specialize (H3 _ Hlt).
    eapply poset_trans; eauto.
Qed.    

Lemma  List_le_antisym{P:PPO} : forall (l1 l2:List P),
List_le l1 l2 -> List_le  l2 l1 -> l1 = l2.
Proof.
intros l1 l2 Hl1l2.
induction Hl1l2; intro Hl2l3.
-
  now inversion Hl2l3.
-
  f_equal.
  apply nth_ext with (d := ppo_bot) (d' := ppo_bot); auto.
  intros n Hlt.
  apply poset_antisym.
  +
    now apply H0.
  +
    inversion Hl2l3; subst.
    apply H4.
    now rewrite H3.
Qed.   



Definition List_Poset(P:PPO) : Poset :=
{|
  poset_carrier := List P;
  poset_le := List_le;
  poset_refl := List_le_refl;
  poset_trans := List_le_trans;
  poset_antisym := List_le_antisym
|}.

Definition List_PPO(P:PPO) : PPO :=
{|
  ppo_poset := List_Poset P;
  ppo_bot := list_bot P;
  ppo_bot_least := List_le_bot
|}.

Lemma LIST2List_monotonic{P:PPO}: 
forall (L1 L2 : LIST_PPO P),  L1 <= L2 ->
List_le (LIST2List L1) (LIST2List L2).  
Proof.
intros L1 L2 Hle.
unfold LIST2List; cbn.
inversion Hle; subst; cbn.
-  
 constructor.
-
  cbn.
  constructor.
  + 
    now do 2 rewrite length_EXP2list.
  +  
  intros i Hlt.
  rewrite length_EXP2list in Hlt.
  do 2 (erewrite nth_EXP2LIST; eauto).
  Unshelve.
  assumption.
Qed.
    

Lemma List2LIST_monotonic{P:PPO}: 
forall (L1 L2 : List_PPO P), List_le L1  L2 ->
@poset_le  (LIST_PPO P) (List2LIST (@ppo_bot P) L1) 
(List2LIST ppo_bot L2).
Proof.
intros L1 L2 Hle.
unfold List2LIST.
inversion Hle.
-
  cbn.
  constructor. 
-
  destruct l1, l2; cbn in H; try lia.
  *
    apply sum_le_refl.
  * 
     cbn.
     unfold list2EXP.
     cbn.
     apply PeanoNat.Nat.succ_inj in H.
     rewrite H.
     constructor.
     intro j.
     destruct j; cbn.
     destruct nval.
     --
      apply (H0 0); cbn; lia.
     --
      apply  (H0 (S nval)); cbn; lia.
Qed.



Lemma LIST2List_rev_monotonic{P:PPO}: 
forall (L1 L2 : LIST_PPO P), 
List_le (LIST2List L1) (LIST2List L2) ->  L1 <= L2.
Proof.
intros L1 L2 Hle.
replace L1 with  (List2LIST ppo_bot (LIST2List L1)); 
[| now rewrite LIST2List2LIST].
replace L2 with  (List2LIST ppo_bot (LIST2List L2));
[| now rewrite LIST2List2LIST].
now apply List2LIST_monotonic.
Qed.
   
Lemma LIST2List_injective{P:PPO}: forall (L1 L2 : LIST_PPO P),
(LIST2List L1) =
(LIST2List L2) ->  L1 = L2.
Proof.
intros L1 L2 Heq.
apply poset_antisym;
 apply LIST2List_rev_monotonic;
 rewrite Heq;
 apply List_le_refl.
Qed.


Lemma List2LIST_rev_monotonic{P:PPO}: 
forall (L1 L2 : List_PPO P),
@poset_le  (LIST_PPO P) (List2LIST (@ppo_bot P) L1) 
(List2LIST ppo_bot L2) -> List_le L1  L2.
Proof.
intros l1 l2 Hle.
replace l1 with  (LIST2List (List2LIST ppo_bot l1));
[| now rewrite List2LIST2List].
replace l2 with  (LIST2List (List2LIST ppo_bot l2));
[| now rewrite List2LIST2List].
now apply LIST2List_monotonic.
Qed.

Lemma List2LIST_injective{P:PPO}: forall (L1 L2 : List_PPO P),
(List2LIST ppo_bot L1) =
(List2LIST ppo_bot L2) ->  L1 = L2.
Proof.
intros L1 L2 Heq.
apply poset_antisym;
 apply List2LIST_rev_monotonic;
 rewrite Heq;
 apply poset_refl.
Qed.


Definition bij_LIST_PPO_List_PPO{P:PPO}: BIJECTION (LIST_PPO P) (List_PPO P):=
{|
  to := LIST2List;
  from := List2LIST ppo_bot;
  to_from := List2LIST2List ppo_bot;
  from_to := LIST2List2LIST ppo_bot
|}. 

Definition ppo_iso_LIST_PPO_List_PPO{P:PPO} : Poset_ISOMORPHISM (LIST_PPO P) (List_PPO P):=
  {|
   b:= bij_LIST_PPO_List_PPO;
   to_mono := LIST2List_monotonic;
   from_mono := List2LIST_monotonic
  |}.

Program
Definition List_CPO(C:CPO) : CPO :=
{|
  cpo_ppo := List_PPO C;
  cpo_lub := 
    fun S => match (oracle (is_directed S )) with
    left Hd => (proj1_sig  
    (@cpo_from_poset_iso (LIST_CPO C) (List_PPO C) 
    ppo_iso_LIST_PPO_List_PPO S Hd))
   | right _ => list_bot _
    end
  ;
  cpo_lub_prop :=_
|}.

Next Obligation.
cbn.
intros.
destruct ( oracle (is_directed (P := List_Poset C) S) ); 
[| contradiction].
apply (proj2_sig 
(@cpo_from_poset_iso  (LIST_CPO C) (List_PPO C) 
 ppo_iso_LIST_PPO_List_PPO S i)).
 Qed.


Lemma LIST2List_cont{P: CPO}: 
 is_continuous (P1:= LIST_CPO P)(P2 := List_CPO P) LIST2List.
Proof.
remember (@ppo_iso_cpo_iso  (LIST_CPO P) (List_CPO P) 
(@ppo_iso_LIST_PPO_List_PPO P)) as Hci.
replace LIST2List with (to Hci); [| now rewrite HeqHci].
apply to_is_continuous.
Qed.


Lemma List2LIST_cont{P: CPO}: 
 is_continuous (P1:= List_CPO P)(P2 := LIST_CPO P) 
 (List2LIST ppo_bot).
Proof.
remember (@ppo_iso_cpo_iso  (LIST_CPO P) (List_CPO P) 
(@ppo_iso_LIST_PPO_List_PPO P)) as Hci.

replace (List2LIST ppo_bot) with (from Hci); [| now rewrite HeqHci].
apply from_is_continuous.
Qed.

Lemma my_algebraic_dir{A : ALGEBRAIC}:
forall (c : List_CPO A), is_directed (compacts_le c).
Proof.
intro c.
cbn in c.
specialize (@ppo_iso_LIST_PPO_List_PPO A) as Hi.
apply Poset_ISOMORPHISM_sym in Hi.
eapply isomorphic_directed_rev with (Iso := Hi).
specialize (@algebraic_dir (LIST_ALGEBRAIC A) (to Hi c)) as Had.
replace 
((@fmap (List_PPO A) (LIST_PPO A) (@compacts_le
(List_CPO A) c) (@to (List_PPO A) (LIST_PPO A) Hi))) with
(@compacts_le (LIST_ALGEBRAIC A)(@to (List_PPO A)(LIST_PPO A) Hi c)); auto.
remember   (Poset_ISOMORPHISM_sym _ _ Hi) as Hi'.
specialize (@ppo_isomorphic_compact_le (LIST_CPO A)(List_CPO A) Hi' (from Hi' c))  as Hcle.
rewrite to_from in *.
now subst.
Qed.




Lemma my_algebraic_lub{A:ALGEBRAIC}:
forall (c : List_CPO A), c = cpo_lub (compacts_le c).
Proof.
intro c.  
apply is_lub_cpo_lub_eq.
specialize (@ppo_iso_LIST_PPO_List_PPO A) as Hi.
apply Poset_ISOMORPHISM_sym in Hi.
unshelve erewrite <- ppo_isomorphic_compact_le.
-
 exact (LIST_ALGEBRAIC A).
-
 apply Hi.
-
 cbn in c.
 specialize (@algebraic_lub (LIST_ALGEBRAIC A) (to Hi c)) as Hala.
 specialize (cpo_lub_prop (compacts_le (P:= LIST_ALGEBRAIC A) (to Hi c)) (algebraic_dir (a:= LIST_ALGEBRAIC A)  (to Hi c))) as Hclp.
 rewrite <- Hala in Hclp.
 clear Hala.
 remember (to Hi c) as c'.
 replace c with (from Hi (to Hi c)); [|apply from_to]. 
rewrite <- Heqc'.
rewrite to_from.
remember ((compacts_le  (P:= LIST_ALGEBRAIC A)  c')) as S'.
now apply lub_fmap_iso.
-
 apply my_algebraic_dir.
Qed.


Lemma LIST2List_compact{P:CPO}:
forall (L : LIST P), is_compact (P:= LIST_CPO P) L -> 
    is_compact (P := List_CPO P) (LIST2List L).
Proof.
intros L Hc.
remember (@ppo_iso_cpo_iso  (LIST_CPO P) (List_CPO P) 
(@ppo_iso_LIST_PPO_List_PPO P)) as Hci.
remember  (@isomorphic_compact _ _ Hci) as Hic.
replace LIST2List with (to Hci); [| now rewrite HeqHci].
now apply Hic.
Qed.


Lemma List2LIST_compact{P:CPO}:
forall (L : List P), is_compact (P:= List_CPO P) L -> 
    is_compact (P := LIST_CPO P) (List2LIST ppo_bot L).
Proof.
intros L Hc.
remember (@ppo_iso_cpo_iso  (LIST_CPO P) (List_CPO P) 
(@ppo_iso_LIST_PPO_List_PPO P)) as Hci.
remember (CPO_ISOMORPHISM_sym _ _ Hci) as Hci'.
remember  (@isomorphic_compact _ _ Hci') as Hic'.
replace (List2LIST ppo_bot) with (to Hci'); 
[now apply Hic' |].
now subst.
Qed.


Definition List_ALGEBRAIC (A:ALGEBRAIC): ALGEBRAIC :=
{|
  algebraic_cpo := List_CPO A;
  algebraic_dir := my_algebraic_dir;
  algebraic_lub :=my_algebraic_lub
|}.



Program Definition List_completion (P:PPO)(M:COMPLETION P) : 
  COMPLETION (List_PPO P) :=
  {|
    alg := List_ALGEBRAIC M;
    inject := fun x =>  
    LIST2List (@inject _ (LIST_completion P M) ((List2LIST ppo_bot x)));
    rev_inj := fun c =>
    match (oracle (is_compact c)) with
    left _ => LIST2List (@rev_inj _ (LIST_completion P M) (List2LIST ppo_bot c)) 
    | right _ => list_bot _
   end 
  |}.


Next Obligation.
intros; reflexivity.
Qed.

Next Obligation.
intros P M p p'.
split; intro Hle.
- 
  apply LIST2List_monotonic; auto.
  rewrite <- (inject_bimono (LIST_completion P M)). 
  now apply List2LIST_monotonic.
-
 apply LIST2List_rev_monotonic in Hle.
 rewrite <- (inject_bimono (LIST_completion P M)) in Hle.
 now apply List2LIST_rev_monotonic in Hle.
Qed. 


Next Obligation.
intros.
apply LIST2List_compact.
apply (@inject_compact (LIST_PPO P) (LIST_completion P M)).
Qed.


Next Obligation.
intros.
unfold "°".
destruct (oracle (is_compact cc)) as [Hc | n];
[| exfalso; now apply n].
split; intro Heq.
-
 rewrite <- Heq.
 rewrite LIST2List2LIST.
 rewrite inject_rev_inj; 
  [now rewrite List2LIST2List |].
 now apply List2LIST_compact.
-
 rewrite <- Heq.
 rewrite LIST2List2LIST.
 rewrite rev_inj_inject.
 now rewrite List2LIST2List.
 Qed.



Program Definition nrev{N: nat} (i : BELOW N) : BELOW N :=
{|nval := N - 1 - (nval _ i) |}.
Next Obligation.
intros N i.
destruct i.
cbn.
lia.
Qed.

Lemma nrev_inv{N:nat} : forall (i : BELOW N), 
 nrev  (nrev  i) = i.
 Proof.
 intro i.
 destruct i.
 unfold nrev.
 cbn.
 apply BELOW_equal.
 lia.
 Qed.


Definition frev{C:CPO} (L : LIST_CPO C) :=
match L with
| sum_bot _ => sum_bot _
| sum_inj _ N f => sum_inj _ N (fun i : BELOW N => f (nrev i))
end.

Lemma frev_inv{C:CPO} (L : LIST_CPO C) : frev (frev L) = L.
Proof.
destruct L; auto.
cbn.
f_equal.
extensionality i.
now rewrite nrev_inv.
Qed.

Lemma frev_mono{C:CPO} : 
is_monotonic (P1 := LIST_CPO C) (P2 := LIST_CPO C) frev.
Proof.
intros L L' Hle.
inversion Hle; subst.
- 
 constructor.
-
 constructor.
 intros i .    
 assert (Ha : forall i, p1 i <= p2 i); [apply H |].
 apply Ha.
 Qed.


Lemma frev_is_continuous{C:CPO} : 
is_continuous (P1 := LIST_CPO C) (P2 := LIST_CPO C) frev.
Proof.
rewrite continuous_iff_mono_commutes.
split; [apply frev_mono |].
intros S l Hd Hl. 
destruct Hl as (Hu & Hl) .
split.
- 
  intros y (z & Hm & Heq); subst.
  apply frev_mono.
  now apply Hu.
 -
  intros y Huy.
  replace y with (frev (frev y)); [| now apply frev_inv].
  apply frev_mono.
  apply Hl.
  intros u Hmu.
  replace u with (frev (frev u)); [| now apply frev_inv].
  apply frev_mono.
  apply Huy.
  now apply member_fmap.
 Qed. 


Definition revb{T:Type}(f : List T) : List T :=
match f with
list_bot _ => list_bot _
|list_inj _ l => list_inj _ (rev l)
end.

Lemma revb_frev{P:CPO}: (*forall (f : List_CPO P),*)
revb  = (LIST2List ° (frev(C:= P)° (List2LIST ppo_bot ))).
Proof.
extensionality f.
destruct f; auto.
cbn.
f_equal.
apply nth_ext with (d := ppo_bot)(d' := ppo_bot).
-
 cbn.
 rewrite length_EXP2list.
 apply rev_length.
-
 rewrite rev_length.
 intros n Hlt.
 unshelve erewrite nth_EXP2LIST; eauto.
 unfold list2EXP.
 cbn.
 rewrite rev_nth; auto.
 f_equal.
 lia.
 Qed.


Lemma revb_is_monotonic{P:CPO}:
is_monotonic (P1 := List_Poset P)(P2 := List_Poset P) revb.
Proof.  
rewrite revb_frev.
apply (comp_is_monotonic
 (P1 := List_Poset P)   
  (P2 := LIST_Poset P) 
  (P3 := List_Poset P)).
- 
 intros x y Hle.
 now apply LIST2List_monotonic.
-
 apply  (comp_is_monotonic
 (P1 := List_Poset P)   
  (P2 := LIST_Poset P) 
  (P3 := LIST_Poset P)).
  +
   apply frev_mono.
  +
    intros x y Hle.
    now apply List2LIST_monotonic.
Qed.     

Lemma revb_is_continuous{P:CPO}:
is_continuous (P1 := List_CPO P)(P2 := List_CPO P) revb.
Proof.  
rewrite revb_frev.
apply (comp_is_continous 
 (P1 := List_CPO P)   
  (P2 := LIST_CPO P) 
  (P3 := List_CPO P)).
- 
 apply LIST2List_cont.
-
 apply (comp_is_continous 
 (P1 := List_CPO P)   
  (P2 := LIST_CPO P)
  (P3 := LIST_CPO P)).
  +
   apply frev_is_continuous.
  +
   apply List2LIST_cont.
Qed.     

Definition mapb{T1 T2: Type}(f : T1 -> T2)(l : List T1):
List T2 :=
match l with
list_bot _ => list_bot _
| list_inj _ l' => list_inj _ (map f l')
end.



Lemma is_directed_in_LIST_aux(T : CPO) :
  forall (S : Setof (LIST T)),
    is_directed  (P := LIST_PPO T) S ->
    S = single (LIST_bot T) \/
      (S <>  single (LIST_bot T) /\
         exists (j:nat) Sj,  remove S (LIST_bot T)  =
                      fmap Sj (sum_inj _ j) /\
                      is_directed (P:= EXP_PPO (BELOW j) T) Sj).
Proof.
intros S.
now rewrite (is_directed_in_sum_iff 
  (fun n => EXP_CPO (BELOW n) T)).
Qed.


Lemma is_directed_in_LIST(T : CPO) :
  forall (S : Setof (LIST T)),
    is_directed  (P := LIST_PPO T) S ->
    S = single (LIST_bot T) \/
      (S <>  single (LIST_bot T) /\
         exists (j:nat) (Sj: Setof (EXP (BELOW j) T)),  
            remove S (LIST_bot T)  =
                      fmap Sj (sum_inj _ j) /\
                      forall d, 
                      is_directed (P:= T) (proj Sj d)).
Proof.
intros S Hd.
destruct (is_directed_in_LIST_aux T S Hd) as
 [Hs | (Hns & j & Sj & Heqr & Had)]; [now left|right].
split; auto.
exists j, Sj.
split; auto.
intro d.
now apply directed_proj.
Qed.          


Definition listproj{T: Type}(S : Setof (list T))(n : nat)(d:T) :=
 (fun (t:T) => exists l, member S l /\ t = nth n l d).
  

Lemma fmap_single{T: PPO}(S : Setof (List T)):
 @fmap (List_PPO T)
          (LIST_PPO T) S
          (@List2LIST T
             (@ppo_bot T))=
 single (LIST_bot T)
<->
S = single (list_bot T).
Proof.
split; intro Heq.
-
subst.
 apply set_equal; intros ; split; intro Hml.
 +
  rewrite member_single_iff.
  assert (Hm' :
    member (@fmap (List_PPO T)
    (LIST_PPO T) S
    (@List2LIST T
       (@ppo_bot T))) (List2LIST ppo_bot x))
  by (now apply member_fmap).
  rewrite Heq in Hm'.
  rewrite member_single_iff in Hm'.
  destruct x; auto.
  discriminate.
 +
  rewrite member_single_iff in Hml.
  rewrite set_equal in Heq.
  specialize (Heq (List2LIST ppo_bot x)).
  rewrite member_single_iff,Hml in  Heq.
  assert (Hm' : member
  (fmap S
     (List2LIST
        ppo_bot))
  (List2LIST ppo_bot
     (list_bot T))) by (now rewrite Heq).
  destruct Hm' as (x' & Heq' & Heq''); subst.
  apply List2LIST_injective in Heq''.
  now rewrite Heq''.
-
subst.
apply set_equal; intros ; split; intro Hml.
+
 destruct Hml as (y & Hs & Heq); subst.
 rewrite member_single_iff in *.
 unfold single in *;subst.
 reflexivity.
+
 rewrite member_single_iff in Hml.
 exists (list_bot T); split; auto.
 apply member_single.
 Qed. 


Lemma is_directed_in_List{T : CPO} :
  forall (S : Setof (List T)),
    is_directed  (P := List_PPO T) S ->
    S = single (list_bot T) \/
      (S <>  single (list_bot T) /\
         exists (j:nat) (S' : Setof (list T)),
         remove S (list_bot T) = fmap S' (list_inj _) /\
            (forall l, member S' l ->  length l = j) /\
                      forall i, i < j -> 
                      is_directed (P:= T) 
                      (listproj S' i ppo_bot)).
Proof.
intros S Hd.
remember (fmap S (List2LIST ppo_bot)) as SL.
assert (Hm : is_monotonic (P1:= List_PPO T)
(P2:= LIST_PPO T) (List2LIST ppo_bot))
by (intros x y Hle;
now  apply List2LIST_monotonic).
specialize (monotonic_directed 
  (P1:= List_PPO T)
  (P2:= LIST_PPO T)
  S (List2LIST ppo_bot) Hm Hd) as HdSL.
subst.
remember (@fmap (List_PPO T)
(LIST_PPO T) S
(@List2LIST T
   (@ppo_bot T))) as SL.
assert (HSeq:  SL = single (LIST_bot T) -> 
   S = single (list_bot T)) by
(intro ; rewrite <- fmap_single;
  now subst).
destruct (is_directed_in_LIST _ SL HdSL) as
[Heqs | (Hneqs & j & sj & Heqr & Had)]; 
[left; now apply HSeq|right; clear HSeq].
assert(HSneq : S <> single (list_bot T)) by
(intro Heq'; apply Hneqs;rewrite HeqSL;
now rewrite <- fmap_single in Heq').
split; auto.
exists j, (fmap sj (EXP2list j)).
split.
{
  apply set_equal; intro l ; split; intro Hml.
  -
   destruct Hml as (Hml & Hneql).
   destruct l ; [clear Hneql| exfalso; now apply Hneql].
   exists l; split; auto.
   assert (HSL :
     member (remove SL (LIST_bot T)) 
      (List2LIST ppo_bot (list_inj _ l))).
     {
      split.
      - 
      rewrite HeqSL; now exists (list_inj _ l).
      -
       cbn; intro; discriminate.
     }
   assert (Hmsj : member 
   (fmap sj
         (sum_inj
            (fun n : nat => EXP (BELOW n) T)
            j))
    (List2LIST ppo_bot (list_inj T l))) by
    now rewrite <- Heqr.
   destruct Hmsj as (e & Hmb & Heqbig).
   exists e; split; auto.
   assert (HeqLL :
    LIST2List (List2LIST ppo_bot (list_inj T l))
   =
   LIST2List (sum_inj
     (fun n : nat => EXP (BELOW n) T)
     j e)) by now apply f_equal.
    rewrite  List2LIST2List in HeqLL.
    cbn in HeqLL.
    now injection HeqLL.
  -  
   destruct Hml as (l' & (Hml' & Heq')); subst.
   eexists; [| intro Habs; discriminate].
   cbn in Hml'.
   assert (HMRS : member 
   (fmap sj
   (sum_inj
      (fun n : nat =>
       EXP (BELOW n) T) j))  (List2LIST ppo_bot (list_inj _ l'))).
   {
    cbn in Heqr.
    cbn.
    destruct Hml' as (x & Hsjx & Heq); subst.
    exists x; split; auto.
    rewrite length_EXP2list.
    now rewrite EXP2list2EXP.
   }
   cbn in Heqr, HMRS.
   rewrite <- Heqr in HMRS.
   destruct HMRS as (HMRS & _).
   destruct HMRS as (z & Hmz & Heqz); subst.
   cbn in Heqz.
   assert (Heqz' : 
   LIST2List (sum_inj
         (fun n : nat => EXP (BELOW n) T)
         (length l')
         (list2EXP ppo_bot (length l') l')) =
       LIST2List (List2LIST ppo_bot z)
   ) by now f_equal.
   cbn in Heqz'.
   rewrite List2LIST2List in Heqz'.
   rewrite list2EXP2list in Heqz'; auto.
   now rewrite Heqz'.  
}
split.
{
intros l Hml.
assert (Hml' : 
member 
(remove SL (LIST_bot T))
(List2LIST ppo_bot (list_inj _ l))).
{
  cbn in Heqr.
  cbn.
  unfold LIST in Heqr.
  rewrite Heqr.
  destruct Hml as (x & (Hsjx & Heq)); subst.
  rewrite length_EXP2list.
  rewrite EXP2list2EXP.
  now exists x.
}
destruct Hml' as (Hml' & _).
rewrite HeqSL in Hml'.
destruct Hml' as (z & Hmz & Heqz); subst.
apply List2LIST_injective in Heqz.
destruct Hml as (x & (Hsjx & Heq)); subst.
now rewrite length_EXP2list.
}
intros i Hlt.
specialize (Had {|nval := i; is_below := Hlt|}).
destruct Had as (Hne & Had).
split.
-
 rewrite not_empty_member in *.
 destruct Hne as (x & Hmx).
 exists x.
 destruct Hmx as (y & Hmy & Heq); subst.
 exists (EXP2list _ y).
 split; [now exists y |].
 now rewrite nth_EXP2LIST with (Hi := Hlt).
-
 intros x y Hmx Hmy.
 specialize (Had x y).
 assert (Hh1 : member
 (proj sj
    {| nval := i; is_below := Hlt |}) x).
 {
   destruct Hmx as (z & Hmz & Heqy); subst.
   destruct Hmz as (u & Hmu & Hequ); subst.
   rewrite nth_EXP2LIST with (Hi := Hlt).
   now exists u.
 }   
 assert (Hh2 : member
 (proj sj
    {| nval := i; is_below := Hlt |}) y).
 {
   destruct Hmy as (z & Hmz & Heqy); subst.
   destruct Hmz as (u & Hmu & Hequ); subst.
   rewrite nth_EXP2LIST with (Hi := Hlt).
   now exists u.
 }
 specialize (Had Hh1 Hh2).
 destruct Had as (z & Hmz & Hle1 & Hle2).
 exists z; split; auto.
 destruct Hmz as (u & Hmu & Hequ); subst.
 exists (EXP2list j u); split; 
 [now exists u |].
 now rewrite nth_EXP2LIST with (Hi := Hlt).
 Qed.


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




Definition list_le{P:PPO}(l1 l2 : list P) :=
  length l1 = length l2 /\
  forall i, i < length l1 ->
  nth i l1 ppo_bot <= nth i l2 ppo_bot.


Lemma list_le_refl{P:PPO}: forall (l: list P),
list_le l l.
Proof.
intro l.
split; auto.
intros i Hlt.
apply poset_refl.
Qed.


Lemma list_le_trans{P:PPO}: forall (l1 l2 l3: list P),
list_le l1 l2 -> list_le l2 l3 -> list_le l1 l3.
Proof.
intros l1 l2 l3 (Heql1 & Heqll1)  (Heql2 & Heqll2) .
split; [congruence|].
intros i Hlt.
eapply poset_trans; eauto.
apply Heqll2.
now rewrite Heql1 in Hlt.
Qed.


Lemma list_le_antisym{P:PPO}: forall (l1 l2: list P),
list_le l1 l2 -> list_le l2 l1 -> l1 = l2.
Proof.
intros l1 l2 (Heql1 & Heqll1)  (Heql2 & Heqll2) .
apply nth_ext with (d := ppo_bot)(d' := ppo_bot); 
[now rewrite Heql1 |].
intros n Hlt.
apply poset_antisym.
-
  now apply Heqll1.
-
  apply Heqll2.
  now rewrite Heql1 in Hlt.
Qed.  


Definition list_Poset(P:PPO) : Poset :=
{|
  poset_carrier := list P;
  poset_le := list_le;
  poset_refl := list_le_refl;
  poset_trans := list_le_trans;
  poset_antisym := list_le_antisym
|}.


Definition get_list{X:Type}(L : List X):
list X :=
match L with
 list_bot _ => nil
 | list_inj _ l => l
end.


Lemma map_cont_aux{P1 P2 : CPO}:
forall (l: list P1) (S: Setof (EXP_CPO P1 P2))(T : Setof (List P2)),
is_directed S -> 
 T = fmap S
         (fun g : EXP_CPO P1 P2 =>
          list_inj P2 (map g l)) ->
forall 
(S': Setof (list P2)),
is_directed (P := list_Poset P2) S' -> 
remove T (list_bot P2) = fmap S' (list_inj P2) ->
forall (j : nat),    
 length l = j ->
 forall (f: EXP P1 P2),  S f -> 
is_lub (P := list_Poset P2)  S' (map (fun d : P1 => cpo_lub (proj S d)) l).
Proof.
intros l S T HdS HeqT S' HdS' HeqS' j  Hlj f  Hmf.
assert (HeqS'' : S' = fmap T get_list).
{
  apply set_equal; intro x; split; intro Hmx.
  -
   subst.
   assert (Hm3 :member (remove
   (fmap S
      (fun g : EXP_CPO P1 P2 =>
       list_inj P2 (map g l)))
   (list_bot P2)) (list_inj P2 x))
   by (rewrite HeqS';
     now exists x).
   destruct Hm3 as ((g & Hmg & Heq ) & _); 
    subst.
   injection Heq; clear Heq ; intro Heq;
   rewrite Heq; clear Heq.
   exists (list_inj _ (map g l)); split; auto.
   now exists g.
  -
   destruct Hmx as (u & Hmu & Heq); subst.
   destruct Hmu as (g & Hmg & Heq); subst.
   cbn in *.
   assert (Hm4: member (remove
   (fmap S
      (fun g : EXP P1 P2 =>
       list_inj P2 (map g l)))
   (list_bot P2)) (list_inj _ (map g l))).
   {
    split; [| intro; discriminate].
    now exists g.
   }
   rewrite HeqS' in Hm4.
   destruct Hm4 as (w & Hmw & Heq); subst.
   injection Heq; clear Heq ; intro Heq;
   now rewrite Heq.
}
assert (Hg:  S' = fmap S (fun g => (map g l))).
{
 rewrite HeqS''.
 apply set_equal; intro x; split; intro Hmx.
 -
  destruct Hmx as (L & Hmu & Heq); subst.
  destruct Hmu as (g & Hmg & Heq); subst.
  cbn.
  now exists g.
-
  destruct Hmx as (u & Hmu & Heq); subst.
  exists (list_inj _ (map u l)); split; auto.
  now exists u.
}
rewrite Hg.
clear HeqS''.  
split.
-
 intros x Hmx.
 destruct Hmx as (u & Hmu & Heq); subst.
 split; [now do 2 rewrite map_length |rewrite map_length].
 intros i Hlt.
 rewrite nth_indep with (d' := u ppo_bot); 
  [|now rewrite map_length].
 rewrite map_nth.
 remember  (u (nth i l ppo_bot)) as v.
 remember (fun d : P1 => cpo_lub (proj S d)) as g. 
 rewrite nth_indep with (d' := g ppo_bot); 
  [|now rewrite map_length].
rewrite map_nth.
subst.
specialize (directed_proj S (nth i l ppo_bot) HdS) as Hdp.
specialize (cpo_lub_prop _ Hdp) as Hil.
destruct Hil as (Hu & Hm).
apply Hu.
now exists u.
-
 intros y Hu.
 assert (Hmmm : member
 (fmap S
    (fun g : EXP_CPO P1 P2 => map g l))
 (map f l)) by now exists f.
 specialize Hu as Hu'.
 specialize (Hu' (map f l) Hmmm).
 destruct Hu' as (Hlu & Hllu).
 rewrite map_length in Hlu.
 split; [now rewrite map_length|rewrite map_length].
 intros i Hlt.
 remember (fun d : P1 => cpo_lub (proj S d)) as h.
 rewrite nth_indep with (d' := h ppo_bot); 
 [| now rewrite map_length].
 rewrite map_nth.
 rewrite Heqh; clear Heqh h.
 assert (Hllu' :  forall i : nat,
   i < length l ->
   f (nth i l (@ppo_bot P1)) <=
   nth i y (@ppo_bot P2)).
  {
    intros k Hlk.
    rewrite map_length in Hllu.
    specialize (Hllu _ Hlk).
    rewrite nth_indep 
     with (d' := f ppo_bot) in Hllu ; 
      [| now rewrite map_length].
    now rewrite map_nth in Hllu.   
  }
 clear Hllu.
 specialize (directed_proj S (nth i l ppo_bot) HdS) as Hdp. 
 specialize (cpo_lub_prop _ Hdp) as Hil.
 destruct Hil as (Hv & Hm).
 apply Hm.
 intros x (u & Hmu & Heq); subst.
 cbn in *.
 unfold is_upper in Hu.
 specialize (Hu (map u l)).
 assert (Hmuu : member
 (fmap S
    (fun g : EXP P1 P2 => map g l))
 (map u l)) by now exists u.
 specialize (Hu Hmuu).
 destruct Hu  as (Hul & Hull).
 rewrite map_length in *.
 specialize (Hull _ Hlt).
 rewrite nth_indep with (d' := u ppo_bot) in Hull;
  [| now rewrite map_length].
 now rewrite map_nth in Hull.
Qed.
 

Lemma mapb_continuous_in_func{P1 P2: CPO} : 
forall (l : List P1),
is_continuous (P1 := EXP_CPO P1 P2) (P2 := List_CPO P2)
 (fun g => mapb g l).
Proof.
intros [l|];
[| cbn ; apply 
   (@cst_is_continous(EXP_CPO P1 P2)  (List_CPO P2))].
intros S Hd; split.
{
 apply monotonic_directed; auto.
 intros x y Hle.
 now apply mapb_monotonic_in_func.
}
cbn [mapb]. 
specialize (lub_proj _ Hd) as Hlp.
specialize (cpo_lub_prop _ Hd) as Hlc.
apply is_lub_unique with (x := cpo_lub S) in Hlp; auto.
rewrite Hlp.
clear Hlp.
remember (fmap S (fun g => mapb g (list_inj P1 l)))
 as T.
assert (HdT : is_directed (P := List_PPO P2) T).
{
 subst.
 apply @monotonic_directed; auto.
 intros x y Hle.
 now apply mapb_monotonic_in_func.
}
destruct (is_directed_in_List _ HdT) as
[HeqS | (HneqS & Hex)].
{
 subst.
 cbn in HeqS.
 rewrite set_equal in HeqS.
 specialize (HeqS (list_bot _)).
 rewrite member_single_iff in HeqS.
 assert (HmS : member
 (fmap S
    (fun g : EXP P1 P2 =>
     list_inj P2 (map g l)))
 (list_bot P2)) by intuition; clear HeqS.
 destruct HmS as (u & Hmu & Heq); subst.
 discriminate.
}
destruct Hex as (j & S' & Hr & Ha1 & Ha2).
specialize HdT as Haux.
specialize Haux as (Hne & _).
specialize (@cpo_lub_prop (List_CPO P2) _ HdT) as Hclp.

cbn [mapb] in HeqT.
specialize (@is_lub_remove_bot 
 (List_PPO P2) T (@cpo_lub (List_CPO P2) T) Hne HneqS) as Hrb.
assert (Hlr: @is_lub (List_PPO P2)
(@remove
   (List_PPO P2) T
   (@ppo_bot
      (List_PPO P2)))
(@cpo_lub
   (List_CPO P2) T)) by intuition.
clear Hrb.   
replace (@ppo_bot
              (List_PPO P2)) with (list_bot P2) in Hlr; auto.
cbn [List_PPO] in Hlr.   
replace (@remove (List_PPO P2) T (list_bot P2))
 with ( @remove (List P2) T (list_bot P2)) in Hlr; auto.
rewrite Hr in Hlr.
specialize (not_empty_not_single_2dif T _ Hne HneqS) 
 as H2d.
destruct H2d as (y & Hmy & Hney). 
specialize 
 (@remove_bot_directed 
 (List_PPO P2) T y HdT Hmy Hney) as Hrb.
 replace (@ppo_bot
 (List_PPO P2)) with (list_bot P2) in Hrb; auto. 
 replace (@remove (List_PPO P2) T (list_bot P2))
 with ( @remove (List P2) T (list_bot P2)) in Hrb; auto. 
 rewrite Hr in Hrb.
specialize (@cpo_lub_prop (List_CPO P2) _ Hrb) as Hlp.
specialize Hlp as Hlp'.
apply is_lub_unique with (x := cpo_lub (c:= List_CPO P2)T) in Hlp; auto.
rewrite HeqT in Hlp.
cbn [mapb] in Hlp.
replace (@fmap (EXP_CPO P1 P2)
(List_CPO P2) S
(fun g : EXP_CPO P1 P2 =>
 list_inj P2
   (@map P1 P2 g l))) with 
(@fmap (EXP_CPO P1 P2)
           (List P2) S
           (fun g : EXP_CPO P1 P2 =>
            list_inj P2
              (@map P1 P2 g l))) ; auto.
rewrite Hlp.
clear Hlp.

assert (HdS' : is_directed (P := list_Poset P2) S').
{
 apply (@rev_monotonic_directed (list_Poset P2) (List_Poset P2) S')
 with (f := list_inj P2); auto.
 intros u v Hle.
 now inversion Hle.
}
assert (Hlub' : forall l',
  is_lub (P := list_Poset P2) S' l' ->
   cpo_lub (c:= List_CPO P2) (fmap S' (list_inj P2)) = list_inj P2 l').
{
 intros l' Hlub'.
 assert (Hlub'' : 
 is_lub (P := List_Poset P2) (fmap S' (list_inj P2)) (list_inj P2 l')).
 {
   split.
   -
   intros x (ll & Hmll' & Heq); subst.
   destruct Hlub' as (Hu & Hm).
   specialize (Hu _ Hmll').
   destruct Hu as (Heql & Heqll).
   constructor; auto.  
   -
    cbn.
    intros z Hu.
    destruct Hlub' as (Hv & Hm).
    destruct z.
    {
    assert (Hu' : is_upper (P := list_Poset P2) S' l0).
    {
      intros x Hmx.
      assert (Hmm : member (fmap S' (list_inj P2))
      (list_inj P2 x)) by now exists x.
      specialize (Hu (list_inj _ x) Hmm).
      inversion Hu; subst; split; auto.
    }
    specialize (Hm _ Hu').
    destruct Hm as (Hl & Hll).    
    constructor; auto.
  }
   destruct HdS' as (Hne' & _).
   rewrite not_empty_member in Hne'.
   destruct Hne' as (w & Hmw).
   assert (Hmm : member (fmap S' (list_inj P2))
      (list_inj P2 w)) by now exists w.
   specialize (Hu _ Hmm).
   inversion Hu.  
 }
  eapply is_lub_unique; eauto.
}
 specialize (Hlub' (map
 (fun d : P1 => cpo_lub (proj S d))
 l)).
 rewrite Hlub'; auto.
 clear Hlub'.
 rewrite HeqT in Hmy.
 destruct Hmy as (f & HSx & Heq).
 rewrite Heq in * ; clear Heq.
 cbn in f.
 assert (HlT :
  member (remove T (list_bot P2)) 
  (list_inj _ (map f l))).
 {
  split; [| intro ; discriminate].
  rewrite HeqT.
  now exists f.
 }
 rewrite Hr in HlT.
 destruct HlT as (l' & Hml' & Heq).
 injection Heq ; clear Heq; intros Heq.
 rewrite <- Heq in *; clear Heq.
 specialize Ha1 as Hlj.
 specialize (Hlj _ Hml').
 rewrite map_length in Hlj.
 rewrite HeqT in Hr.
 subst.
 eapply map_cont_aux ; eauto.
Qed.

