(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 10,  Estudio de un caso: compilación de expresiones aritméticas y booleanas *)


Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZArith.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Open Scope Z_scope.



(* Expresiones aritméticas *)

Definition vname:=string.

Definition val:=Z.

Inductive AExp :=
 |Var : vname -> AExp
 |Cons : Z -> AExp
 |Add : AExp -> AExp -> AExp.
 

Definition State := vname -> val.

Fixpoint eval (e:AExp) (s:State):=
 match e with
  | Var x => s x
  | Cons z => z
  | Add e1 e2 => eval e1 s + eval e2 s
 end.


Inductive AInstr:=
 |LoadC: Z -> AInstr
 |LoadV: vname -> AInstr
 |AddI: AInstr.


Definition stack:=list Z.

Print hd.

Fixpoint ej (i:AInstr) (s:State) (p:stack) :=
 match i with
  | (LoadC n) => n::p
  | (LoadV x) => s x :: p
  | AddI =>  (hd 0  p + hd 0 (tl p)) :: tl (tl p)
 end.


Definition program := list AInstr.

Fixpoint ejp (p:program) (s:State) (q:stack) :=
 match p with
  | nil => q
  | (i::is) => ejp is s (ej i s q)
 end.


Fixpoint compile (e:AExp):=
 match e with
  | Var x => [LoadV x]
  | Cons z => [LoadC z]
  | Add e1 e2 => compile e1 ++ compile e2 ++ [AddI]
 end.


Lemma append_ejp: forall (p1 p2:program) (s:State) (r:stack),
                   ejp (p1++p2) s r = ejp p2 s (ejp p1 s r).
Admitted.                     


Lemma eval_compile_gen: forall (e:AExp) (s:State) (p:stack), 
                          ejp (compile e) s p = (eval e s)::p.
Proof.
induction e.
simpl.
trivial.
intros.
simpl.
trivial.
intros.
simpl.
rewrite append_ejp.
rewrite IHe1.
rewrite append_ejp.
rewrite IHe2.
simpl.
replace (eval e2 s + eval e1 s) with (eval e1 s + eval e2 s).
trivial.
ring.
Qed.

Theorem eval_compile_correct: forall (e:AExp) (s:State), ejp (compile e) s nil = [eval e s].
Proof.
intros.
apply eval_compile_gen.
Qed.


(* Extensión con expresiones booleanas *)

Check (sum Z bool).

Check inl.


Definition ZB:= sum Z bool.

Check ZB.

Check inr.

Check ((inr Z) bool).

Definition injb:=((inr Z) bool).

Check injb.

Check inl.

Check (inl(A:=Z) bool).

Definition injz:= (inl(A:=Z) bool).

Check injz.


Inductive ABExp :=
 |NVar : vname -> ABExp
 |CInt : Z -> ABExp
 |ETrue : ABExp
 |EFalse : ABExp
 |Plus : ABExp -> ABExp -> ABExp
 |Neg : ABExp -> ABExp. 

Definition StateZB:= vname -> ZB.

Fixpoint evalAB (e:ABExp) (s:StateZB): option ZB :=
 match e with
  | NVar x => Some (s x)
  | CInt z => Some (injz z)
  | ETrue => Some (injb true)
  | EFalse => Some (injb false)
  | Plus e1 e2 => match evalAB e1 s,evalAB e2 s with
                   |Some (inl v1),Some (inl v2) => Some (injz (v1+v2))
                   | _, _ => None
                  end
  | Neg e => match (evalAB e s) with
              |Some (inr b) => Some (injb (negb b))
              | _ => None
             end
 end.


Inductive ABInstr:=
 |LoadCInt: Z -> ABInstr
 |LoadNVar: vname -> ABInstr
 |LoadETrue: ABInstr
 |LoadEFalse: ABInstr
 |PlusI: ABInstr
 |NegI: ABInstr.


Fixpoint compileAB (e:ABExp):=
 match e with
  | NVar x => [LoadNVar x]
  | CInt z => [LoadCInt z]
  | ETrue => [LoadETrue]
  | EFalse => [LoadEFalse]
  | Plus e1 e2 => compileAB e1 ++ compileAB e2 ++ [PlusI]
  | Neg e => compileAB e ++ [NegI]
 end.

(*
Theorem ABeval_compile_correct: forall (e:ABExp) (s:State), 
         ejpAB (compileAB e) s nil = [evalAB e s].
Proof.
*)

