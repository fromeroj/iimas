(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Tarea 2. Razonamiento ecuacional y especificación/verificación de tipos abstractos de datos.
   Entregar la solución en un archivo llamado NombreT2.v
   La fecha de entrega es el domingo 16 de marzo a las 2359hrs.
*)

Require Import Setoid.
Set Implicit Arguments.
Definition admite_def {T: Type} : T.  Admitted.
Section AlgebrasBooleanas.

Hypotheses (A:Set)
           (z e:A)  (* z es el cero (vacío, false) y e es el uno (total,true) *)
           (m j:A -> A -> A)  (* m es el meet (unión,disyunción) y j es el join (intersección,conjunción) *)
           (c:A -> A).   (* c es el complemento *)

Infix "&" := m (at level 40). 
Infix "#" := j (at level 40).
Axiom iasoc  : forall x y z : A, x & (y & z) = (x & y) & z. 
Axiom uasoc  : forall x y z : A, x # (y # z) = (x # y) # z. 
Axiom iconm  : forall x y : A, x & y  = y & x. 
Axiom uconm  : forall x y : A, x # y =  y # x. 
Axiom iabs   : forall x y : A, y & (x # y)  = y. 
Axiom uabs   : forall x y : A, y # (x & y) = y. 
Axiom uId    : forall x : A, x # (c x) = e.
Axiom iZero  : forall x : A, x & (c x) = z.
Axiom uidistr: forall x y z : A, z # (x & y)  = (z # x) & (z # y).
Axiom iudistr: forall x y z : A, z & (x # y)  = (z & x) # (z & y).

Theorem ieIdI: forall x:A, e & x = x.
Proof.
intros.
assert (H:= iabs (c x) x).
assert (H0:= uId x ).
rewrite <- H0, iconm, uconm.
exact H.
Qed.

Theorem ieIdD: forall x:A, x & e = x. 
intros.
rewrite iconm;apply ieIdI.
Qed.

Theorem ueNtI: forall x:A, e # x = e.
Proof.
intros.
assert ( J:= ieIdD x);rewrite <- J.
apply uabs.
Qed.

Theorem ueNtD: forall x:A, x # e = e.
intros.
rewrite uconm;apply ueNtI.
Qed.

Theorem uzIdI: forall x:A, z # x = x.
intros.
assert (H:= uabs  (c x) x );rewrite iconm in H.
assert (I:= iZero x);rewrite I in H.
rewrite uconm.
exact H.
Qed.

Theorem uzIdD: forall x:A, x # z = x.
intros.
rewrite uconm;apply uzIdI.
Qed.

Theorem izNtI: forall x:A, z & x = z.
intros.
assert (H:= iabs x z).
assert (H1:= uzIdD x );rewrite H1 in H.
exact H.
Qed.

Theorem izNtD: forall x:A, x & z = z.
intros.
rewrite iconm;apply izNtI.
Qed.

Theorem unic_comp: forall x y:A, x # y = e -> x & y = z -> y = c x.
intros.
assert (J0:= ieIdD (c x) );rewrite <- J0,<- H.
assert (J2:= iudistr x y (c x));rewrite J2.
rewrite iconm in H0.
assert (J3:= iZero x);rewrite iconm, J3, iconm,<- H0.
assert (J4:= iudistr x (c x) y);rewrite <- J4.
assert (J5:=uId x);rewrite J5.
assert (J6:= ieIdD y);rewrite J6.
reflexivity.
Qed.

Theorem uidemp: forall x:A, x # x = x.
intros.
assert (H:= ieIdD  (x # x) );rewrite <-H.
assert (J:= uId x);rewrite <- J.
assert (K:= uidistr x (c x) x); rewrite <-K.
assert (L:= iZero x); rewrite L.
apply uzIdD.
Qed.

Theorem iidemp: forall x:A, x & x = x.
intros.
assert (H:= uzIdI (x & x)).
assert (H0:= iZero x);rewrite <- H.
rewrite <- H0.
assert (H1:= iudistr (c x) x x);rewrite <- H1.
assert (c x # x = e ).
rewrite uconm.
apply uId.
rewrite H2.
apply ieIdD.
Qed.

Print option.

Section Pilas.

  Variable (B:Type).

  Inductive stack: Type :=
    | empty : stack 
    | push : B -> stack -> stack.

Definition pop (s:stack):option stack :=
  match s with
    |empty => None
    |push H t => Some t
  end.

Definition top (s:stack):option B :=  (* definir correctamente *)
  match s with
    |empty => None
    |push H t => Some H
  end.

Theorem nil_not_push: forall (x:B) (s:stack), empty <> (push x s).
Proof.
  intros.
  discriminate.
  Qed.

Theorem case_stack: forall (s:stack), s = empty \/ exists x:B, exists p:stack, s = push x p.
Proof.
intro.
induction s.
left;reflexivity.
right.
destruct s.
Case s  empty.



destruct IHs.
right.
exists b,s.
reflexivity.
right.





Admitted.



Admitted.


Theorem top_empty: forall s:stack, top s = None -> s = empty.
Proof.
intro.
compute.
intro.


apply nil_not_push.

unfold top.

assert (s=empty).



compute.

apply top.

inversion s.

discriminate.

destruct top.
compute.

discriminate.
Admitted.



Lemma stack_cons: forall (x:B) (s p:stack), top p = Some x -> pop p = Some s -> p = push x s.
intros.
induction p.

discriminate.


Admitted.

Lemma top_non_empty : forall s:stack, s <> empty -> exists x:B, top s = Some x.
Admitted.

Theorem unit_stack: forall s:stack, pop s = Some empty -> exists x:B, s = push x empty.
Admitted.



End Pilas.
