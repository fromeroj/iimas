(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 9,  Estudio de un caso: expresiones aritméticas y polinomios *)


Require Import Coq.Lists.List.
Require Import ZArith.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Open Scope Z_scope.


(* Expresiones aritméticas *)

Inductive Exp :=
 |X : Exp
 |Cons : Z -> Exp
 |Add : Exp -> Exp -> Exp
 |Mult: Exp -> Exp -> Exp.


Fixpoint eval (e:Exp) (v:Z): Z :=
 match e with
  | X => v
  | Cons n => n
  | Add e1 e2 => eval e1 v + eval e2 v
  | Mult e1 e2 => eval e1 v * eval e2 v
 end.



(* Polinomios *)

Definition Poly := list Z.


Fixpoint evalp (p:Poly) (v:Z):Z :=
 match p with
  | [] => 0
  | (c::cs) => c + v * (evalp cs v)
 end.


Fixpoint sumap (p q:Poly):Poly :=
 match p,q with
  | [],q => q 
  | (c::cs),[] => p
  | (c::cs), (d::ds) => c+d :: sumap cs ds
 end.


Fixpoint prodp (p q:Poly):Poly :=
 match p with
  | [] => []
  | (c::cs) =>  [] 
 end.


Fixpoint coefs (e:Exp):Poly :=
 match e with
  | X => [0,1]
  | (Cons z) => [z]
  | Add e1 e2 => [] 
  | Mult e1 e2 => []
 end.




(* Correctud de la evaluación: evaluar una expresión en un valor dado es lo mismo que transformar la expresión a un polinomio y evaluar dicho polinomio en el mismo valor
*)

Theorem eval_evalp_correct: forall (v:Z) (e:Exp), eval e v = evalp (coefs e) v.
Admitted.
