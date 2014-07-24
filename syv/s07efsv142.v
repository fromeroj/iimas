(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 7,  Razonamiento Ecuacional *)

Require Import Setoid.

Section Grupos.

Hypotheses (A:Set)
           (e:A)  (* Elemento neutro *)
           (m:A -> A -> A)  (* Operacion del grupo mul x y = x * y *)
           (i:A -> A). (* Inverso i x = x^-1*)

Infix "&" := m (at level 40).

Axiom asoc : forall x y z : A, x & (y & z) = (x & y) & z. (* x*(y* z)=(x*y)*z *)

Axiom idI : forall x:A, e & x = x.  (* e*x = x *)

Axiom invI : forall x:A, (i x) & x = e.  (* x^-1 * x = e *)


Theorem ej1: forall x y:A,  (x & y) & (e & x) = x & (y & x).
Proof.
intros.
rewrite idI.
rewrite asoc.
reflexivity.
Qed.


Theorem UnicIdI: forall x:A, x & x = x -> x = e.
Proof.
intros.
rewrite <- idI with x.
rewrite <- (invI x).
rewrite <- asoc.
rewrite H.
trivial.
Qed.


Theorem UnicIdIv2: forall x:A, x & x = x -> x = e.
Proof.
intros.
rewrite <- idI with x.
rewrite <- (invI x) at 1.
rewrite <- asoc.
rewrite H.
rewrite invI.
trivial.
Qed.


Theorem invD: forall x:A, x & (i x) = e.
Proof.
intros.
apply UnicIdI.
(* rewrite asoc. *)
rewrite <- asoc with x (i x) (x & i x).
(* rewrite asoc. *)
rewrite asoc with (i x) x (i x).
rewrite invI.
rewrite idI.
trivial.
Qed.


Theorem idD: forall x:A, x & e = x.
Proof.
intros.
rewrite <- (invI x).
rewrite asoc.
rewrite invD.
rewrite idI.
trivial.
Qed.

Lemma congI: forall x y z:A, x = y -> x & z = y & z.
Proof.
intros.
rewrite H.
trivial.
Qed.

Lemma congD: forall x y z:A, x = y -> z & x = z & y.
Proof.
intros.
rewrite H.
trivial.
Qed.

Lemma CanI: forall x y z:A, x & y = x & z -> y = z.
Proof.
intros.
rewrite <- idI.
rewrite <- (idI y).
rewrite <- invI with x.
rewrite <- asoc.
rewrite <- asoc.
apply congD.
trivial.
Qed.


Lemma CanD: forall x y z:A, y & x = z & x -> y = x.
Admitted.


Theorem NeuID:  forall e':A, (forall x:A, m e' x = x) -> e = e'.
Proof.
intros.
rewrite <- idD with e'.
rewrite H.
reflexivity.
Qed.


Theorem UnicInv: forall x y:A, x & y = e -> x = i y.
Admitted.

Theorem invinv: forall x:A, i (i x) = x.
Proof.
intros.
symmetry.
apply UnicInv.
exact (invD x).
Qed.


Theorem invop: forall x y:A, i (x & y) = (i y) & (i x).
Proof.
intros.
symmetry.
apply UnicInv.
rewrite asoc.
rewrite <- asoc with (i y) (i x) x.
rewrite invI.
rewrite idD.
exact (invI y).
Qed.





(* Ejercicios: probar a1-a3 *)

Hypothesis a1: (forall x y:A, (i x) & (x & y) = y).
Hypothesis a2: (i e) = e.
Hypothesis a3: (forall x y:A, y & ((i y) & x) = x).

Axiom asocS : forall x y z : A, (x & y) & z = x & (y & z).


(* El siguiente conjunto de ecuaciones es completo para
  la teoría de los grupos

J W Klop: Term rewriting systems in Handbook of Logic
in Computer Science, vol 2, p 49. *)

Hint Rewrite idI idD asocS invI invD invinv invop
a1 a2 a3: rtgrupos.


Theorem ej1v2: forall x y:A,  (x & y) & (e & x) = x & (y & x).
Proof.
intros.
autorewrite with rtgrupos.
trivial.
Qed.


Theorem ej2: forall x y z :A, x & (i (y & (z &  x))) & y & z = e.
Proof.
intros.
Admitted.


Theorem ej2auto: forall x y z :A, x & (i (y & (z &  x))) & y & z = e.
intros.
autorewrite with rtgrupos.
trivial.
Qed.



(* Tarea *)

Theorem Ord2Abel: (forall z:A, z & z = e) -> forall x y : A, x & y = y & x.
Admitted.



End Grupos.



