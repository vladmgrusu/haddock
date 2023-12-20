From Corec Require Export While.

Definition partial_hoare
  {S A : Type} (P : S -> Prop) (m : program S A) (Q : A -> S -> Prop) : Prop :=
forall s s' a, P s -> m s = Some (a, s') -> Q a s'.

Notation "{{ P }} m {{ Q }}" :=
(partial_hoare P m Q)
  (at level 90,
   format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'"
  ).

Lemma weaken
  {S A : Type} (m : program S A) (P Q : S -> Prop) (R : A -> S -> Prop) :
{{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros Hm Himpl s s' a Hs Heq.
eapply Hm; [apply Himpl, Hs | exact Heq].
Qed.

Lemma strengthen
  {S A : Type} (m : program S A) (P : S -> Prop) (Q R : A -> S -> Prop) :
{{ P }} m {{ Q }} -> (forall a s, Q a s -> R a s) -> {{ P }} m {{ R }}.
Proof.
intros Hm Himpl s s' a Hs Heq.
eapply Himpl, Hm; [exact Hs | exact Heq].
Qed.

Lemma bind_rule
  {S A B : Type} (m : program S A) (f : A -> program S B)
  (P : S -> Prop) (Q : A -> S -> Prop) (R : B -> S ->  Prop) :
(forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} ->
{{ P }} do x <- m; f x {{ R }}.
Proof.
intros Hf Hm s s' b Hs Heq1.
unfold bind in Heq1.
destruct (m s) as [[a s''] | ] eqn: Heq2; [ | discriminate Heq1].
eapply Hf; [ | exact Heq1].
eapply Hm; [exact Hs | exact Heq2].
Qed.

Lemma seq_rule
  {S A B : Type} (m1 : program S A) (m2 : program S B)
  (P : S -> Prop) (Q : S -> Prop) (R : B -> S ->  Prop) :
{{ Q }} m2 {{ R }} -> {{ P }} m1 {{ fun _ s => Q s }} ->
{{ P }} m1;; m2 {{ R }}.
Proof.
intros Hm2 Hm1.
exact (bind_rule m1 (fun _ => m2) P (fun _ s => Q s) R (fun _ => Hm2) Hm1).
Qed.

Lemma ret_triple {S A : Type} (a : A) (P : A -> S -> Prop) :
{{ fun s => P a s }} ret a {{ P }}.
Proof.
intros s s' a' Hs Heq.
unfold ret in Heq.
congruence.
Qed.

Lemma get_triple {S : Type} (P : S -> S -> Prop) :
{{ fun s => P s s }} get {{ P }}.
Proof.
intros s s' s'' Hs Heq.
unfold get in Heq.
congruence.
Qed.

Lemma put_triple {S : Type} (s : S) (P : unit -> S -> Prop) :
{{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s' s'' [] Hs Heq.
unfold put in Heq.
congruence.
Qed.

Lemma modify_triple {S : Type} (f : S -> S) (P : unit -> S ->  Prop) :
{{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
unfold modify.
eapply bind_rule.
- intro s.
  apply put_triple.
- eapply weaken; [apply get_triple | ].
  cbn.
  tauto.
Qed.

Lemma if_rule
  {S A : Type} (cond : program S bool) (m1 m2 : program S A)
  (P : S -> Prop) (Q : bool -> S -> Prop) (R : A -> S -> Prop) :
{{ P }} cond {{ Q }} -> {{ Q true}} m1 {{ R }} -> {{ Q false}} m2 {{ R }} ->
{{ P }} If cond then m1 else m2 {{ R }}.
Proof.
intros Hcond Hm1 Hm2.
unfold ifthenelse.
eapply bind_rule.
- intros [ | ].
  + exact Hm1.
  + exact Hm2.
- exact Hcond.
Qed.

Lemma while_fuel_rule
  (fuel : nat) {S : Type} (cond : program S bool) (body : program S unit)
  (I : bool -> S -> Prop) :
{{ I true }} cond {{ I }} ->
{{ I true }} body {{ fun _ s' => I true s' }} ->
{{ I true }} while_fuel fuel cond body {{ fun _ s' => I false s' }}.
Proof.
intros Hcond Hbody.
induction fuel as [ | fuel IH]; [intros ? ? ? ? [=] | ].
cbn.
unfold whileF.
eapply if_rule.
- exact Hcond.
- eapply seq_rule.
  + exact IH.
  + exact Hbody.
- eapply weaken.
  + apply ret_triple.
  + cbn.
    tauto.
Qed.

Lemma while_rule
  {S : Type} (cond : program S bool) (body : program S unit)
  (I : bool -> S -> Prop) :
{{ I true }} cond {{ I }} ->
{{ I true }} body {{ fun _ s' => I true s' }} ->
{{ I true }} While cond {{ body }} {{ fun _ s' => I false s' }}.
Proof.
intros Ht1 Ht2 s s' a Ht Ha.
rewrite while_fuel_while_some in Ha.
destruct Ha as (fuel & Hfuel).
apply 
(while_fuel_rule fuel cond body I Ht1 Ht2 s s' a Ht Hfuel). 
Qed.
