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
  | (c::cs) => sumap (map (fun x:Z => c*x) q) (prodp cs (0::q))  
 end.


Fixpoint coefs (e:Exp):Poly :=
 match e with
  | X => [0,1]
  | (Cons z) => [z]
  | Add e1 e2 => sumap (coefs e1) (coefs e2) 
  | Mult e1 e2 => prodp (coefs e1) (coefs e2)
 end.




(* Correctud de la evaluación: evaluar una expresión en un valor dado es lo mismo que transformar la expresión a un polinomio y evaluar dicho polinomio en el mismo valor
*)

Lemma evalp_sumap: forall (v:Z) (p q:Poly), evalp (sumap p q) v = evalp p v + evalp q v.
Proof.
intros v p.
induction p.
simpl.
trivial.
intros.
destruct q.
simpl.
ring.
simpl.
rewrite IHp.
ring.
Qed.


Lemma evalp_map: forall (c v:Z) (q:Poly), evalp (map (fun x:Z => c*x) q) v = c * evalp q v.
Proof.
intros.
induction q.
simpl.
ring.
simpl.
rewrite IHq.
ring.
Qed.



Lemma evalp_prodp: forall (v:Z) (p q:Poly), evalp (prodp p q) v = evalp p v * evalp q v.
Proof.
intros v p.
induction p.
intros.
simpl.
trivial.
intros.
simpl.
rewrite evalp_sumap.
rewrite evalp_map.
rewrite IHp.
simpl.
ring.
Qed.



Theorem eval_evalp_correct: forall (v:Z) (e:Exp), eval e v = evalp (coefs e) v.
Proof.
intros.
induction e.
simpl eval.
simpl coefs.
replace (evalp [0,1] v) with (v*(evalp [1] v)).
replace (evalp [1] v) with 1.
ring.
replace (evalp [1] v) with (1+v*0).
ring.
trivial.
trivial.
simpl.
ring.
simpl.
rewrite IHe1.
rewrite IHe2.
rewrite evalp_sumap.
trivial.
simpl.
rewrite IHe1.
rewrite IHe2.
rewrite evalp_prodp.
trivial.
Qed.
