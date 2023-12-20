Definition program (S A : Type) : Type := S -> option (A * S).

Definition ret {S A : Type} (a : A) : program S A :=
fun s => Some (a, s).

Definition bind {S A B : Type} (m : program S A) (f : A -> program S B) :
program S B :=
fun s => match m s with
| None => None
| Some (a, s') => f a s'
end.

Notation "'do' x <- m1 ; m2" := (@bind _ _ _ m1 (fun x => m2))
  (at level 60, x name, m1 at level 50, m2 at level 60).

Notation "m1 ;; m2" := (@bind _ _ _ m1 (fun _ => m2))
  (at level 60, m2 at level 60).

Definition undefined (S A : Type) : program S A :=
fun _ => None.

Definition get {S : Type} : program S S :=
fun s => Some (s, s).

Definition put {S : Type} (s : S) : program S unit :=
fun _ => Some (tt, s).

Definition modify {S : Type} (f : S -> S) : program S unit :=
do s <- get;
put (f s).

Definition ifthenelse
  {S A : Type} (cond : program S bool) (m1 m2 : program S A) : program S A :=
do b <- cond; if b then m1 else m2.

Notation "'If' c 'then' m1 'else' m2" := (ifthenelse c m1 m2) (at level 200).
