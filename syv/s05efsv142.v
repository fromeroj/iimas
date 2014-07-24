(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 5, Logica de predicados *)


Section LogPred.

Hypotheses (A:Type)

           (P Q: A -> Prop)
           (R : A -> A -> Prop)
           (f : A -> A)
           (a b : A).


Check P a.

Check P a -> Q b.

Check R b.

Check R (f a) (f (f b)).

Check forall x:A, R a x -> R x a.

Check exists x:A, ~ R x x.


Theorem Socrates: (forall x:A, P x -> Q x) /\ P a -> Q a.
Proof.
intros.
destruct H as [P1 P2].
apply P1.
exact P2.
Qed.

Print Socrates.

Theorem DistrAY: (forall x:A, P x /\ Q x) <-> (forall x:A,P x) /\ (forall x:A, Q x).
Proof.
unfold iff.
split.
intros.
split.
intro x0.
destruct H with x0.   (* o bien elim H with x0. *)
exact H0.
intro y0.
elim H with y0.
intros C D.
exact D.
intro E.
destruct E as [C1 C2].
intro z0.
split.
apply C1. 
apply C2.
Qed.

Theorem DistrAO: (forall x:A,P x) \/ (forall x:A, Q x) -> (forall x:A, P x \/ Q x).
Proof.
intro.
destruct H as [H1|H2].
intro x0.
left.
apply H1.
intro y0.
right.
apply H2.
Qed.

Theorem AA: (forall x y:A, R x y) -> forall y x: A, R y x.
Proof.
intro H.
intros y0 x0.
apply H.
Qed.


Theorem AMPN: (forall x:A, P x -> ~ Q x) -> (forall x:A, P x) -> forall z:A, ~ Q z.
Proof.
intros H1 H2.
intro z0.
apply H1.
apply H2.
Qed.

(* Require Import Classical. *)


Hypothesis C:Prop.

Theorem PrenexY:  (C /\ forall x:A, P x ) <-> forall x:A, C /\ P x.
Proof.
unfold iff.
split.
intro H.
destruct H.
intro x0.
split.
exact H.
apply H0.
intro K.
split.
destruct K with a.
exact H.
intro z0.
apply K.
Qed.




Theorem Ex1: P a -> exists x:A, P x.
Proof.
intro.
exists a.
trivial.
Qed.


Theorem EDY: (exists x:A, P x /\ Q x) -> (exists x:A, P x) /\ (exists x:A, Q x).
Proof.
intro H.
split.
destruct H.
destruct H.
exists x.
exact H.
elim H. 
intro z0.
intro K.
destruct K as [K1 K2].
exists z0.
exact K2.
Qed.




Theorem EDO: (exists x:A, P x \/ Q x) <-> (exists x:A, P x) \/ (exists x:A, Q x).
Proof.
unfold iff.
split.
intro H.
destruct H.
destruct H as [H1|H2].
left; exists x;trivial.
right; exists x; trivial.
intro I.
destruct I as [I1|I2].
destruct I1.
exists x.
left;exact H.
destruct I2.
exists x;right;exact H.
Qed.


Theorem AE: (exists x:A, forall y:A , R x y) -> forall y:A, exists x:A, R x y.
Proof.
intro H.
intro y0.
destruct H.
exists x.
apply H.
Qed.


Theorem PrenexImp : (exists x:A, P x) -> C <-> forall x:A, P x -> C.
Proof.
unfold iff.
split.
intro H.
intro x0.
intro J.
apply H.
exists x0.
exact J.
intro K.
intro L.
destruct L.
apply K with x.
exact H.
Qed.


Theorem DMorganG: (exists x:A, ~ P x) -> ~ forall x:A, P x.
Proof.
intro.
intro.
destruct H.
apply H.
apply H0.
Qed.













(* Algunos argumentos *)

Theorem Argum1: (forall y:A, P y -> Q y) -> (forall x:A, (exists y:A, P y /\ R x y) -> exists z:A, Q z /\ R x z).
Proof.
intro H.
intro x0.
intro J.
destruct J.
destruct H0 as [H1 H2].
exists x.
split.
apply H.
exact H1.
exact H2.
Qed.

Hypotheses D W O: A -> Prop.

Theorem Arg2: (forall x:A, D x -> W x /\ P x) /\
              (exists x:A, D x /\ O x) ->
              (exists x:A, O x /\ P x).
Proof.
intro H.
destruct H as [H1 H2].
destruct H2.
destruct H as [H3 H4].
exists x.
split.
trivial.
apply H1.
trivial.
Qed.

Theorem Arg3: (forall x:A, D x -> W x) /\
              (~ exists x:A, D x /\ W x) ->
              ~ exists x:A, D x.
Proof.
intro H.
destruct H as [H1 H2].
contradict H2.
destruct H2.
exists x;split;trivial.
apply H1.
trivial.
(* exact (H1 x H). *)
Qed.
End LogPred.



Theorem distrOI: forall (p q r:Prop), p \/ (q -> r) <-> p \/ q -> p \/ r.
Proof.
intros.
unfold iff.
split.
intros.
destruct H0.
left;trivial.
destruct H.
left;trivial.
right.
exact (H H0).



intros.
cut ( p \/ ~p).
intros.
destruct H0.
left;trivial.
right.
cut ( q \/ ~q).
intros.
assert ( p \/ q).
right;trivial.
assert (p \/ r).
exact (H H3).
destruct H4.
elim (H0 H4).
trivial.
