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



Axiom iasoc : forall x y z : A, x & (y & z) = (x & y) & z. 

Axiom uasoc : forall x y z : A, x # (y # z) = (x # y) # z. 

Axiom iconm : forall x y : A, x & y  = y & x. 

Axiom uconm : forall x y : A, x # y =  y # x. 

Axiom iabs : forall x y : A, y & (x # y)  = y. 

Axiom uabs : forall x y : A, y # (x & y) = y. 

Axiom uId :  forall x : A, x # (c x) = e.

Axiom iZero :  forall x : A, x & (c x) = z.

Axiom uidistr: forall x y z : A, z # (x & y)  = (z # x) & (z # y).

Axiom iudistr: forall x y z : A, z & (x # y)  = (z & x) # (z & y).


Theorem ieIdI: forall x:A, e & x = x. 
Admitted.  (* Hay una prueba muy simple usando absorcion*)

Theorem ieIdD: forall x:A, x & e = x. 
Admitted.

Theorem ueNtI: forall x:A, e # x = e.
Admitted. (* Hay una prueba muy simple usando absorcion*)

Theorem ueNtD: forall x:A, x # e = e.
Admitted.  (* Usar adecuadamente ieIdI o ieIdD y absorcion *)

Theorem uzIdI: forall x:A, z # x = x.
Admitted.

Theorem uzIdD: forall x:A, x # z = x.
Admitted.

Theorem izNtI: forall x:A, z & x = z.
Admitted.

Theorem izNtD: forall x:A, x & z = z.
Admitted.

Theorem unic_comp: forall x y:A, x # y = e -> x & y = z -> y = c x.
Admitted. (* Utilizar transitividad con (y # c x) *)

Theorem uidemp: forall x:A, x # x = x.
Admitted.

Theorem iidemp: forall x:A, x & x = x.
Admitted.



Section Pilas.

  Variable (B:Type).

  Inductive stack: Type :=
    | empty : stack 
    | push : B -> stack -> stack.


Print option.  (* El tipo option a corresponde al tipo Maybe a en Haskell *)

Definition pop (s:stack):option stack := error.  (* definir correctamente *)

Definition top (s:stack):option B := error. (* definir correctamente *)



Theorem nil_not_push: forall (x:B) (s:stack), empty <> (push x s).
Admitted.

Theorem case_stack: forall (s:stack), s = empty \/ exists x:B, exists p:stack, s = push x p.
Admitted.

Lemma stack_cons: forall (x:B) (s p:stack), top p = Some x -> pop p = Some s -> p = push x s.
Admitted.

Theorem top_empty: forall s:stack, top s = None -> s = empty.
Admitted.

Lemma top_non_empty : forall s:stack, s <> empty -> exists x:B, top s = Some x.
Admitted.

Theorem unit_stack: forall s:stack, pop s = Some empty -> exists x:B, s = push x empty.
Admitted.





End Pilas.

