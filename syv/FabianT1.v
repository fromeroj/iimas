(* 
   EspecIficación Formal MCIC - Semántica y Verificación LCC
   Fabian Romero
   Tarea
 *)

(*  Problema 1.  

    Defina una funcion recursiva doble:Nat ->Nat y demuestre que para 
    cualquier n:Nat, se cumple que doble n = suma n n  

*)

Fixpoint doble n:nat := 
  match n with
      | 0 => 0
      | S n' => 2 + doble n'
  end.

Theorem doble_n : forall(n:nat), doble n = n + n.
Proof.
intros.
induction n.
unfold doble.
auto.
simpl.
rewrite IHn.
auto.
Qed.

(*  Problema 2

     Defina una funcion cuenta: A -> List A -> Nat que cuenta el numero de presencias
     de un elemento en una lista dado. 
*)

Require Import List.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint cuenta (a: nat) (lst: list nat) : nat :=
  match lst with
    |nil => 0
    |h::t => if (beq_nat a h)
             then (1 + cuenta a t)
             else cuenta a t
  end.

Fixpoint lenght (lst:list nat) :=
  match lst with
    |nil => 0
    |h::t => (1 + lenght t)
  end.

(*
Demuestre que para cualesquiera x:A, xs:List A, se cumple que cuenta x xs ≤ length xs
*)

Theorem cuenta_a :forall (a: nat), forall (b: nat), forall (lst: list nat), cuenta a (b::lst) <= 1 +cuenta a lst.
Proof.
intros.
induction lst.
simpl.
destruct (beq_nat a b);auto.
intros;simpl.
destruct (beq_nat a b);auto.
Qed.


(*  Problema 3 
     Realice lo siguiente acerca de arboles binarios.
*)


(*
Defina un tipo Tree a que implemente árboles binarios posiblemente vacios y con informacion en todos sus nodos.
*)
Inductive Tree : Set :=
| nil_tree : Tree
| cons : Tree->nat->Tree->Tree.

(*
Defina una funcionon flat:Tree a -> List a que devuelva una lista con todos los valores
guardados en el arbol, sin remover duplicados (el orden no es relevante).
*)

Fixpoint flat (t: Tree) : (list nat) :=
  match t with
      |nil_tree => nil
      |cons l1 n1 r1 => n1 :: flat l1 ++ flat r1
  end.

(*
Defina una funcion tsum:Tree Nat -> Nat que sume los valores en un arbol de numeros.
*)

Fixpoint tsum (t: Tree) : nat :=
  match t with
      |nil_tree => 0
      |cons l1 n1 r1 => n1 + (tsum l1) + (tsum r1)
  end.

(*
Defina una funcion lsum:List Nat -> Nat que sume los valores en una lista de n ́
umeros.
*)

Fixpoint lsum (lst: list nat) : nat :=
  match lst with
      |nil => 0
      |h::t => h + lsum t
  end.

(*
Demuestre que para cualquier arbol t:Tree Nat se cumple que
tsum t = lsum (flat t)
*)

Require Import ArithRing.

Theorem lsm : forall (lst: list nat),forall (lst2: list nat), lsum (lst++lst2)=lsum(lst)+lsum(lst2). 
Proof.
intros.
induction lst.
simpl;reflexivity.
simpl;rewrite IHlst.
ring.
Qed.


Theorem flat_sum : forall(t: Tree), tsum t = lsum (flat t). 
Proof.
intros.
induction t.
compute;reflexivity.
simpl.
rewrite lsm.
rewrite IHt1.
rewrite IHt2.
ring.
Qed.


(* Problema 4 *)

Theorem cuatro_a : forall(p: Prop), forall(q : Prop), (p -> q) <-> (p/\q <->p).
Proof.
split;intro.
split;intro.
destruct H0.
assumption.
split.
assumption.
apply H.
assumption.
intro.
destruct H.
apply H1.
assumption.
Qed.

Theorem cuatro_b (c:Prop) (n:Prop) (t:Prop) (s:Prop) (p:Prop) (h:Prop) : (c /\ n -> t ) -> h /\ ~ s -> ( h /\ ~ (s \/ c) -> p) -> n /\ ~t -> p.
Proof.
intros H [H0 H1] H2 [H3 H4].
apply H2.
split.
assumption.
intro.
destruct H5.
absurd s;assumption.
absurd t.
assumption.
apply H.
split;assumption.
Qed.



Theorem cuatro_c (p: Type -> Type -> Type -> Prop) (f: Type -> Type) (a: Type):
  (forall x: Type, p a x x ) -> (forall x:Type, forall y:Type, forall z:Type , p x x y -> p (f x) y (f z) ) -> (exists z:Type, p (f a) z (f (f a))).
Proof.
intros.
exists a.
apply H0.
apply H.
Qed.

