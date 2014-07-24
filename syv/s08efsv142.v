(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 8,  Inducción + razonamiento ecuacional + Inducción en predicados *)



Require Import Setoid.

Search nat.

Check nat.
Print nat.

Check nat_ind.

Search nat.  (* Funciones primitivas: 0,S, pred, plus, mult, minus *)

Print plus.  (* (0+m = m,  S n + m = S (n+m) *)
Print pred.
Print mult.  (* 0 * m = 0,  (S n) * m = m + n * m    *)
Print minus. (* 0-n=0, S k - 0 = S k, S k - S l = k - l *)



Lemma S0: forall n: nat, 0+n =n.
Admitted.



Lemma M0: forall n:nat, 0 * n = 0.
Admitted.


Lemma MS: forall n m:nat, S n * m = m + n * m.
Admitted.

Lemma SS: forall n m:nat, S n + m = S (n + m).
Admitted.


Lemma Suma0: forall n:nat, n + 0= n.
Admitted.


Lemma CSS: forall n m:nat, n + S m = S (n + m).
Admitted.

Lemma ConmSuma: forall n m: nat, n+m = m+n.
Admitted.



Lemma Mult0: forall n:nat, n*0=0.
Admitted.


Require Import ArithRing.  (* Para disponer de la táctica ring en naturales *)


Lemma SumAsoc: forall n m p:nat, (n+m)+p=n+(m+p).
Admitted.

Lemma MDistr: forall n m p:nat, n*(m+p)=n*m + n*p.
Admitted.

Lemma MDistrD: forall n m p:nat, (m+p)* n = m*n + p*n.
Admitted.



Lemma S1S: forall m:nat, m+1=S m.
Admitted.



Lemma NeutroM: forall n:nat, n* (S 0)=n.
Admitted.

Lemma ConmM: forall n m:nat, n * m = m * n.
Admitted.


(* Ejemplo clásico de inducción, fórmula de Gauss *)

Fixpoint sumh (m:nat) :=
 match m with
  |0 => 0
  |S n => sumh n + S n
 end.



Theorem Ind1: forall n:nat, 2 * sumh n = n*(n+1).
Proof.
intros.
induction n.
reflexivity.
simpl sumh.
replace (2 * (sumh n + S n)) with (2*sumh n + 2* S n).
rewrite IHn.
replace (S n) with (n+1).
replace (n * (n + 1) + 2 * (n + 1)) with ((n+1)*(n+1+1)).
trivial.
rewrite <- MDistrD.
replace (n+1+1) with (n+(1+1)).
change (1+1) with 2.
rewrite ConmM.
reflexivity.
rewrite SumAsoc.
reflexivity.
rewrite S1S.
reflexivity.
rewrite <- MDistr.
trivial.
Qed.


Theorem Ind1v2: forall n:nat, 2 * sumh n = n*(n+1).
Proof.
intros.
induction n.
reflexivity.
simpl sumh.
replace (2 * (sumh n + S n)) with (2*sumh n + 2* S n).
rewrite IHn.
replace (S n) with (n+1).
replace (n * (n + 1) + 2 * (n + 1)) with ((n+1)*(n+1+1)).
trivial.
ring.
rewrite S1S.
trivial.
ring.
Qed.



Theorem Ind1v3: forall n:nat, 2 * sumh n = n*(n+1).
Proof.
intros.
induction n.
simpl.
trivial.
simpl sumh.
rewrite MDistr.
rewrite IHn.
ring.
Qed.








(* Ejemplo donde la inducción usual es inconveniente:
   Mostrar que si un número n es par (test en Prop) entonces
   existe un natural p tal que n = 2*p. *)

Fixpoint evenb n :=  
 match n with
  |0 => True
  |S (S p) => evenb p
  |_ => False
 end.

Lemma ev0: evenb 0.
Proof.
simpl.
trivial.
Qed.

Lemma evss: forall n:nat, evenb n -> evenb (S (S n)).
Proof.
intros.
simpl.
trivial.
Qed.

Example ne1: ~ evenb 1.
simpl.
intro.
trivial.
Qed.

Example e2: evenb 2.
simpl.
trivial.
Qed.



Theorem evenbEx2: forall n:nat, evenb n -> exists p:nat, n = 2*p.
Proof.
intros.
induction n.
exists 0.
reflexivity.
Admitted. (* Se admite la prueba pues la HI es demasiado debil *)



Lemma eqneg: forall p q:Prop, (p <-> ~q) -> ( q <-> ~p).
Admitted.

Lemma evno: forall n:nat, evenb (S n) <-> ~ evenb n.
Admitted.


Theorem evenoddEx: forall n:nat, (evenb n -> exists p:nat, n= 2* p) /\  (~ evenb n -> exists p:nat, n= 2* p+1).
Proof.
intros.
induction n.
split.
intro.
exists 0.
reflexivity.
intros.
exfalso.
apply H.
simpl.
trivial.
split.
intro.
cut (~ evenb n).
intro.
destruct IHn.
assert (exists p:nat, n = 2 * p +1).
apply H2.
trivial.
destruct H3.
exists (x+1).
rewrite H3.
ring.
apply evno.
trivial.
intros.
assert (evenb n).
assert (evenb n <-> ~ evenb (S n)).
exact (eqneg (evenb (S n)) (evenb n) (evno n)).
apply H0.
trivial.
destruct IHn.
assert (exists p : nat, n = 2 * p).
exact (H1 H0).
destruct H3.
exists x.
rewrite H3.
ring.
Qed.


(* Predicados inductivos: esto va más allá del poder de un lenguaje funcional y es reminiscente 
del mecanismo de definición de la programación lógica*)

Inductive even:nat -> Prop :=
 |ceven0: even 0
 |cevenS: forall n:nat, even n -> even (S (S n)).

Check even_ind.


Theorem evenEx2: forall n:nat, even n -> exists p:nat, n = 2*p.
Proof.
intros.
induction H.
exists 0;reflexivity.
destruct IHeven.
exists (S x).
rewrite H0.
ring.
Qed.


Example noteven1: ~ even 1.
Proof.
unfold not.
intros.
inversion H.
Qed.


Example even2: even 2.
Proof.
constructor.
constructor.
Qed.


(* Relacion menor o
 igual en naturales <= *)

Print le.   (* n <= n    n <= m -> n <= S m *)
Check le_ind.

Theorem Pos: forall n:nat, 0 <= n.
Proof.
intros.
induction n.
constructor.
constructor.
trivial.
Qed.

Theorem sucmq: forall n m:nat, n <= m -> S n <= S m.
Proof.
intros.
induction H.
constructor 1.
constructor 2.
trivial.
Qed.

Theorem Mp: forall n p:nat, n <= p + n.
intros.
induction p.
rewrite S0.
apply (le_n).
replace (S p + n) with (S (p+n)).
apply (le_S).
trivial.
simpl.
trivial.
(* constructor 1.
constructor 2.
trivial. *)
Qed.


Theorem exmqs: forall n m:nat, n<= m -> exists p:nat, m = p+n.
Proof.
intros.
induction H.
exists 0.
reflexivity.
destruct IHle.
exists (S x).
rewrite H0.
trivial.
Qed.



Lemma dsum0: forall m p:nat, m = p + m -> p = 0.
Proof.
intros.
induction m.
rewrite Suma0 in H.
symmetry.
trivial.
apply IHm.
rewrite CSS in H.
injection H.
trivial.
Qed.


Lemma dsum2: forall p q:nat, 0 = p + q -> p = 0 /\ q = 0.
Proof.
intros.
induction p.
split.
trivial.
simpl in H.
symmetry.
trivial.
simpl in H.
contradict H.
discriminate.
Qed.


Lemma mmi: forall m n:nat, m < n -> m <= n.
Admitted.

Lemma marefl: forall n:nat, ~ (n < n).
Admitted.

Lemma dicot: forall n m:nat, n <= m <-> ~(m<n).
Admitted.

Theorem mqex: forall m n:nat, (exists p:nat, m = p + n) -> n <= m.
Proof.
intros.
apply dicot.
unfold not.
intros.
cut (exists p:nat, n = p + m).
intros.
destruct H as [p].
destruct H1 as [q].
assert ( n = q + p + n).
rewrite H1 at 1.
rewrite H.
ring.
assert (q=0 /\ p = 0).
apply dsum2.
symmetry.
apply (dsum0 n).
trivial.
destruct H3.
assert (n = m).
rewrite H3 in H1.
replace (0+m) with m in H1.
trivial.
apply S0.
rewrite H5 in H0.
apply (marefl m).
trivial.
apply exmqs.
apply mmi.
trivial.
Qed.


Theorem trans_ex: forall p n m:nat, p<=m -> n<=p -> n<=m.
Proof.
intros.
apply mqex.
assert (exists r0:nat, m = r0 + p).
apply exmqs.
trivial.
assert (exists s0:nat, p = s0 + n).
apply exmqs.
trivial.
destruct H1 as [r0].
destruct H2 as [s0].
exists (r0+s0).
rewrite H2 in H1.
rewrite H1.
ring.
Qed.

Theorem transmq: forall n p m:nat, n<=p -> p<=m -> n<=m.
Proof.
intros.
induction H0.
trivial.
constructor.
trivial.
Qed.

Theorem smc: forall n m:nat, S n <= S m -> n <=m.
Proof.
intros.
inversion H.
constructor.
apply transmq with (S n).
constructor 2.
constructor 1.
trivial.
Qed.


Theorem compsm: forall n m p:nat, n<=p -> n + m <= p + m.
Proof.
intros.
induction H.
constructor 1.
inversion H.
simpl.
constructor.
constructor.
rewrite H1.
simpl.
constructor.
trivial.
Qed.



Theorem compsmI: forall n m p:nat, n<=p -> m + n <= m + p.
Admitted.

Theorem compats: forall n m p q:nat, n <= m -> p <= q -> n+p <= m+q.
Admitted.

Theorem comppm: forall n m p:nat, n <= m -> n*p <= m*p.
Proof.
intros.
induction H.
constructor.
simpl.
rewrite ConmSuma.
rewrite <- (S0 (n*p)) at 1.
rewrite ConmSuma.
apply compats.
trivial.
exact (Pos p).
Qed.


(* Ejemplo ilustrativo de ayuda al ejercicio 2 de la tarea *)

Require Import List.

Print or.

Print sumbool.

SearchAbout sumbool.

Section Remove.



    Hypothesis A:Set.
    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Fixpoint remove (x : A) (l : list A): list A :=
      match l with
        | nil => nil
        | (y::ys) => if (eq_dec x y) then remove x ys else (y::remove x ys)
      end.

    Theorem remove_In : forall (l : list A) (x : A), ~ In x (remove x l).
    Proof.
    induction l.
     auto.
     intro.
     simpl. 
     destruct (eq_dec x a).
     apply IHl. 
     unfold not.   
     intro.
     simpl in H.
     destruct H.
     auto.
     apply (IHl x).
     trivial.
    Qed.

  End Remove.



