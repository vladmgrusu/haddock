From Coq Require Import IndefiniteDescription FunctionalExtensionality
PropExtensionality.
From Corec Require Export Poset.

Record SemiLattice : Type :=
{
sl_poset :> Poset;
sl_top : sl_poset;
sl_top_greatest : forall x, poset_le x sl_top;
sl_lub : forall (S: Setof sl_poset), sl_poset;
sl_lub_prop : forall (S: Setof sl_poset), 
  is_lub S (sl_lub S)
}.


Arguments sl_poset {_}.
Arguments sl_top {_}.
Arguments sl_top_greatest {_} _.
Arguments sl_lub {_} _.
Arguments sl_lub_prop {_} _.


Lemma gfp_sig{L:SemiLattice} : forall (f : L -> L),
is_monotonic f -> 
{x |  is_post_fixpoint f x /\ forall y, 
is_post_fixpoint f y -> poset_le y x}.
Proof.
intros f Hmf.
exists (sl_lub (fun x => is_post_fixpoint f x)).
specialize (sl_lub_prop (fun x => is_post_fixpoint f x)) as Hl.
remember (sl_lub (fun x => is_post_fixpoint f x)) as l.
specialize 
(@lub_is_lub L (fun x : L => is_post_fixpoint f x)
 (ltac: (now exists l) )) as Hl'.
eapply is_lub_unique with (x:= l) in Hl'; auto.
rewrite Hl'.
split.
-
unfold is_post_fixpoint.
apply lub_is_minimal. 
intros x Hmx.
eapply @poset_trans with  (f x).
 +
   apply Hmx.
 +
   apply Hmf.
   apply lub_is_upper.
   apply Hmx.
 - 
  intros y Hp.
  apply lub_is_upper; auto.
Qed.



Definition gfp{L:SemiLattice} 
 (f: L-> L)(Hmf : is_monotonic f):=
 proj1_sig (gfp_sig f Hmf).

Lemma gfp_is_fixpoint{L:SemiLattice} 
 (f: L-> L)(Hm :is_monotonic f) : is_fixpoint f (gfp f Hm).
Proof.
destruct (proj2_sig (gfp_sig f Hm)) as 
(Hp & Hmax).
apply poset_antisym.
 - 
   apply Hp.
 -
  apply Hmax.
  unfold is_post_fixpoint.
  apply Hm.
  apply Hp.
Qed.


Lemma gfp_max{L:SemiLattice} 
 (f: L-> L)(Hm :is_monotonic f) :
forall y, 
is_post_fixpoint f y -> poset_le y (gfp f Hm).
Proof.
intros y Hp.    
now apply (proj2_sig (gfp_sig f Hm)).
Qed.

Lemma to_poset_refl{X:Type}{P:Poset}:
forall (f : X -> P)(x:X), poset_le (f x) (f x).
Proof.
intros f x.
apply poset_refl.
Qed.    


Lemma to_poset_trans{X:Type}{P:Poset}:
forall (f g h: X -> P),
(forall x, poset_le (f x) (g x)) ->
(forall x, poset_le (g x) (h x)) 
-> forall x, poset_le (f x) (h x).
Proof.
intros f g h Hfg Hgh x.
apply @poset_trans with (y := (g x)); auto.
Qed.


Lemma to_poset_antisym{X:Type}{P:Poset}:
forall (f g: X -> P),
(forall x, poset_le (f x) (g x)) ->
(forall x, poset_le (g x) (f x)) 
-> f = g.
Proof.
intros f g Hfg Hgf.
extensionality x.
apply poset_antisym; auto.
Qed.


Definition to_poset{X:Type}{P:Poset}: Poset :=
{| poset_carrier := X -> P;
   poset_le := fun f f' => forall x, poset_le (f x)(f' x); 
   poset_refl := to_poset_refl;
   poset_trans := to_poset_trans;
   poset_antisym := to_poset_antisym
|}.

Lemma to_sl_top_greatest{X:Type}{P:SemiLattice}:
forall (f : X -> P)(x:X), poset_le (f x)  sl_top .
Proof.
intros f x.
apply sl_top_greatest.
Qed.    

Lemma to_sl_lub_prop{X:Type}{P:SemiLattice}:
forall (S: Setof (X -> P)),
@is_lub to_poset S
  (fun x : X =>
   sl_lub (fun y : P => exists f : X -> P, member S f /\ y = f x)).
Proof.
intro S.
split.
- 
 intros f Hmx x.
 cbn in *.
 specialize (sl_lub_prop  ((fun y : P =>
 exists
   f0 : X -> P,
   member S f0 /\
   y = f0 x))) as (Hu & _).
apply Hu.
exists f; auto.
-
 intros f Huf x.
 cbn in *.
 specialize (sl_lub_prop  ((fun y : P =>
 exists
   f0 : X -> P,
   member S f0 /\
   y = f0 x))) as (Hu & Hmin).
 apply Hmin.
 intros y Hmy.
 destruct Hmy as (g & Hmg & Heq);
 subst.
 now apply Huf.
Qed.   


Definition to_semilattice{X:Type}{P:SemiLattice}: SemiLattice :=
{| 
  sl_poset := to_poset (X :=X);
  sl_top := fun _ => sl_top ;
  sl_top_greatest := to_sl_top_greatest;
  sl_lub := fun (S : Setof (X -> P))  => 
   (fun x => sl_lub 
     (fun y =>  exists f,  member S f /\ y = f x));  
  sl_lub_prop := to_sl_lub_prop
|}.






Definition Prop_poset: Poset :=
{| poset_carrier := Prop;
   poset_le := fun p p'  => p -> p';
   poset_refl := ltac:(cbn ; intros; assumption);
   poset_trans := ltac:(cbn; intros; apply H0,H; auto);
   poset_antisym :=
    ltac:(cbn; intros ; 
      apply propositional_extensionality ;split;auto)
|}.


Lemma Prop_lub_prop : forall (S:Setof Prop),
is_lub (P:= Prop_poset) S (exists p:Prop, p /\ member S p).
Proof.
intro S.
split.
- intros p Hmp x.
  cbn in *.
  now exists p.
-
 cbn.
 intros p Hu Hex.
 destruct Hex as (p' & Hp' & Hmp').
 now apply (Hu p').
 Qed.



Definition Prop_semilattice: SemiLattice :=
{| 
  sl_poset := Prop_poset;
  sl_top := True ;
  sl_top_greatest := ltac:(intros x Hx; auto);
  sl_lub := fun (S : Setof Prop)  => 
    exists (p:Prop), p /\ member S p;  
  sl_lub_prop := Prop_lub_prop
|}.



Definition Pred_poset{X:Type}  := 
     @to_poset X Prop_poset.

Definition Pred_semilattice{X:Type}  := 
     @to_semilattice X Prop_semilattice.



Lemma Pred_unfold{X:Type}: forall (F : Setof X -> Setof X)
(Hm : is_monotonic (P1 := Pred_poset) (P2:= Pred_poset) F), 
  (gfp (L:= Pred_semilattice) F Hm)  = (F (gfp (L:= Pred_semilattice) F Hm)).
Proof.
intros F Hm.
now specialize (gfp_is_fixpoint (L:= @Pred_semilattice X) _ Hm) as Hgfp.
Qed.

Lemma pred_coind{X:Type}: forall (F : Setof X -> Setof X)
(Hm : is_monotonic (P1 := Pred_poset) (P2:= Pred_poset) F) 
(S: Setof X), 
subset S (F S)-> 
subset S (gfp (L:= Pred_semilattice) F Hm).
Proof.
intros F Hm S Hsub.
apply (gfp_max (L:= @Pred_semilattice X) _ Hm), Hsub.
Qed.



Definition binary(X Y:Type) := X -> Y -> Prop.


Definition binary_poset{X Y:Type}  := 
     @to_poset X (@to_poset Y Prop_poset).

Definition binary_semilattice{X Y:Type}  := 
     @to_semilattice X (@to_semilattice Y Prop_semilattice).



Lemma binary_unfold{X Y:Type}: forall (F : binary X Y -> binary X Y)
(Hm : is_monotonic (P1 := binary_poset) 
(P2:= binary_poset) F), 
  (gfp (L:= binary_semilattice) F Hm)  = 
  (F (gfp (L:= binary_semilattice) F Hm)).
Proof.
intros F Hm.
now specialize (gfp_is_fixpoint (L:= @binary_semilattice X Y) _ Hm) as Hgfp.
Qed.

Lemma binary_coind{X Y:Type}: forall (F : binary X Y -> binary X Y)
(Hm : is_monotonic (P1 := binary_poset) (P2:= binary_poset) F) 
(S : binary X Y), 
(forall x y, S x y -> (F S) x y)-> 
forall x y, S x y -> (gfp (L:= binary_semilattice) F Hm) x y.
Proof.
intros F Hm S Hsub.
apply (gfp_max (L:= @binary_semilattice X Y) _ Hm).
intros x y Hle.
now apply Hsub.
Qed.



