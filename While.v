From Coq Require Import FunctionalExtensionality Lia.
From Corec Require Export Exp Option Haddock Monad.



Definition If_Seq
  {S : Type} (cond : program S bool) 
  (body : program S unit) (q : program S unit): program S unit :=
If cond then (body ;; q) else ret tt.


Lemma  If_Seq_monotonic {S : Type}
 (cond : program S bool)  (body : program S unit): 
is_monotonic 
(P1 :=  (EXP_Poset S (option_Poset (unit*S)))) 
(P2 :=  (EXP_Poset S (option_Poset (unit*S)))) 
(If_Seq cond body).
Proof.
intros x y Hle s.
unfold If_Seq, ifthenelse,bind.
destruct (cond s) eqn:Heqc; [| apply @poset_refl].
destruct p.
destruct b eqn : Heqb;  [| apply @poset_refl].
destruct (body s0);  [| apply @poset_refl].
destruct p.
apply Hle.
Qed.

 
Lemma  If_Seq_H_continuous {S : Type}
 (cond : program S bool)  (body : program S unit): 
is_H_continuous (B :=(option_CPO (unit*S))) (If_Seq cond body).
Proof.
split; [apply  If_Seq_monotonic|].
intros P Hd.
extensionality s.
specialize Hd as (Hne & _).
unfold  If_Seq,ifthenelse,bind.
destruct (cond s) eqn:Heqc;
  [ |  rewrite  fmap_const_single; [now rewrite cpo_lub_single| assumption]].
destruct p.
destruct b eqn : Heqb; 
   [ |  rewrite  fmap_const_single; [now rewrite cpo_lub_single| assumption]].
destruct (body s0) eqn: Heqbd; 
   [ |  rewrite  fmap_const_single; [now rewrite cpo_lub_single| assumption]].
 destruct p.
reflexivity.
Qed.



Definition whileF
  {S : Type} (cond : program S bool) (f : program S unit -> program S unit)
  (body : program S unit) : program S unit :=
If cond then (body ;; f body) else ret tt.


Lemma whileF_monotonic {S : Type} (cond : program S bool) :
is_monotonic 
      (P1 :=  EXP_PPO
      (EXP_PPO S (option_PPO (unit*S))) (EXP_PPO S (option_PPO (unit*S))))
      (P2 :=  EXP_PPO
      (EXP_PPO S (option_PPO (unit*S))) (EXP_PPO S (option_PPO (unit*S))))
(whileF cond).
Proof.
intros x y Hle p s.
unfold whileF,ifthenelse,bind.
destruct (cond s) eqn:Heqc; [| apply @poset_refl].
destruct p0.
destruct b eqn : Heqb;  [| apply @poset_refl].
destruct (p s0);  [| apply @poset_refl].
destruct p0.
cbn in  Hle.
apply Hle.
Qed.

Lemma whileF_H_continuous {S : Type} (cond : program S bool) :
is_H_continuous (B := EXP_CPO S (option_CPO (unit*S))) (whileF cond).
Proof.
split; [apply whileF_monotonic |].
intros T Hd.
unfold whileF.
extensionality p.

specialize (If_Seq_H_continuous cond p) as Hcc.
unfold If_Seq in Hcc.
rewrite <- cont_iff_H_cont in Hcc.
destruct Hcc with (S := proj T p).
- 
 now apply directed_proj.
-
 rewrite H0.   
 f_equal.
 apply set_equal; intro x ; split; intro Hmx.
 +
  destruct Hmx as (f & Hf & Heq); subst.
  destruct Hf as (F & HMF & Heq); subst.
  now exists F.
 +
    destruct Hmx as (f & Hf & Heq); subst.
    exists (f p); split; auto.
    now exists f.     
Qed.
 

Definition while {S : Type} (cond : program S bool) (body : program S unit) :
program S unit :=
pointwise_fix (B := EXP_CPO S (option_CPO (unit*S))) (whileF cond) body.

Notation "'While' cond '{{' body }}" := (while cond body).

Lemma while_fixpoint
  {S : Type} (cond : program S bool) (body : program S unit) :
While cond {{ body }} = If cond then (body ;; While cond {{ body}}) else ret tt.
Proof.
assert (Hfix :=
  f_equal
    (fun f => f body)
    (proj1
      (Haddock_pointwise
        (B := EXP_CPO S (option_CPO (unit*S)))
        (whileF cond)
        (whileF_H_continuous cond)))).
unfold is_least_fixpoint, is_fixpoint in Hfix.
unfold while at 1.
rewrite <- Hfix.
reflexivity.
Qed.

Definition while_fuel
  (fuel : nat) {S : Type} (cond : program S bool) (body : program S unit) :
program S unit :=
iterate
  (X :=
    EXP_PPO
      (EXP_PPO S (option_PPO (unit*S))) (EXP_PPO S (option_PPO (unit*S))))
  fuel (whileF cond) body.


Lemma while_fuel_iterations_directed
{S: Type} (cond : program S bool) (body : program S unit):
is_directed
    (fun g : EXP_PPO S (option_PPO (unit * S)) =>
     exists n : nat, g = while_fuel n cond body).
Proof.
split.
- 
 rewrite not_empty_member.
 now exists ( while_fuel 0 cond body), O.
-
 intros x y Hmx Hmy.
 destruct Hmx as (n & Heq); subst.
 destruct Hmy as (m & Heq); subst.
 exists ( while_fuel (max n m) cond body); repeat split.
 +
  now exists (max n m).
 +   
  unfold while_fuel.
  specialize (iterate_mono (X := EXP_PPO (EXP_PPO S (option_PPO (unit * S)))
       (EXP_PPO S (option_PPO (unit * S)))) n (Nat.max n m)(@whileF S cond))
   as Hi.
 cbn in Hi.
 cbn.
 apply Hi; [apply whileF_monotonic | lia].
 +
  unfold while_fuel.
  specialize (iterate_mono (X := EXP_PPO (EXP_PPO S (option_PPO (unit * S)))
       (EXP_PPO S (option_PPO (unit * S)))) m (Nat.max n m)(@whileF S cond))
   as Hi.
 cbn in Hi.
 cbn.
 apply Hi; [apply whileF_monotonic | lia].
Qed.
     

Lemma while_equals
  {S : Type} (cond : program S bool) (body : program S unit):
while cond body =
 fun (s:S) => 
cpo_lub (c := option_CPO (unit * S))
(proj (D := S) (C := option_PPO (unit*S)) 
(fun (g: EXP S (option (unit*S)))  => exists n, g = while_fuel n cond body) s).
Proof. 
specialize (lub_proj (C := (option_CPO (unit * S)))
 (fun g : EXP S (option (unit * S))
         =>
         exists n : nat,
           g = while_fuel n cond body)
            ( while_fuel_iterations_directed cond body)) as Hlp.
specialize (cpo_lub_prop (c := EXP_CPO S (option_CPO (unit * S))) _ 
  (while_fuel_iterations_directed cond body)) as Hclp.
apply is_lub_unique with 
  (x := (@cpo_lub (EXP_CPO S (option_CPO (unit * S)))
        (fun g : EXP_PPO S (option_PPO (unit * S)) =>
       exists n : nat, g = @while_fuel n S cond body))) in Hlp; auto. 
Qed.

Lemma while_fuel_while_some
  {S : Type} (cond : program S bool) (body : program S unit)
  (s : S) (x : unit*S) :
while cond body s = Some x <->
exists fuel, while_fuel fuel cond body s = Some x.
Proof.
rewrite while_equals.
unfold while_fuel.
specialize (while_fuel_iterations_directed cond body) as Hww.
specialize (@directed_proj S (option_PPO (unit*S)) (fun g : EXP_PPO S (option_PPO (unit * S)) =>
           exists n : nat, g = while_fuel n cond body) s Hww) as Hdp.
specialize (@cpo_lub_prop  (option_CPO (unit * S))_ Hdp) as Hcp.
split; intro HH.
-
 specialize (some_lub_member (@proj S (option_PPO (unit * S))
            (fun g : EXP S (option (unit * S)) =>
             exists n : nat,
               g =
               @iterate
                 (EXP_PPO (EXP_PPO S (option_PPO (unit * S)))
                    (EXP_PPO S (option_PPO (unit * S)))) n
                 (@whileF S cond) body) s) x) as Hlp.
 specialize (Hlp Hdp).
 rewrite <- HH in Hlp.
 specialize (Hlp Hcp).
 destruct Hlp as (p & Hmp & Heqp).
 destruct Hmp as (n & Heq); subst.
 rewrite HH in Heqp.
 now exists n.
-
 destruct HH as (n & Heq).
 specialize (@member_lub_some (unit*S) 
 (@proj S (option_PPO (unit * S))
       (fun g : EXP S (option (unit * S)) =>
        exists n0 : nat,
          g =
          @iterate
            (EXP_PPO (EXP_PPO S (option_PPO (unit * S)))
               (EXP_PPO S (option_PPO (unit * S)))) n0
            (@whileF S cond) body) s) x) as Hls. 
 specialize (Hls Hdp).
 assert (Hmm :  @member (option (unit * S))
          (@proj S (option_PPO (unit * S))
             (fun g : EXP S (option (unit * S)) =>
              exists n0 : nat,
                g =
                @iterate
                  (EXP_PPO
                     (EXP_PPO S (option_PPO (unit * S)))
                     (EXP_PPO S (option_PPO (unit * S))))
                  n0 (@whileF S cond) body) s)
          (@Some (unit * S) x)).
 {
   rewrite <- Heq.
   (*Set Printing Implicit.*)
   exists (@iterate
       (EXP_PPO (EXP_PPO S (option_PPO (unit * S)))
          (EXP_PPO S (option_PPO (unit * S)))) n
       (@whileF S cond) body); split; auto.
  now exists n.
 }
 specialize (Hls Hmm).
 apply is_lub_unique with (x := Some x) in Hcp; auto.
Qed.
