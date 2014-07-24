(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 11,  Lenguaje IMP/WHILE 1: expresiones aritméticas y booleanas *)


Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZArith.


(* Esta definición es para poder declarar funciones sin dar su definición *)

Definition admit {T: Type} : T. Admitted.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Open Scope Z_scope.

Open Scope string_scope.


(* Tipo de nombres de variables *)

Definition Vname := string.

(* Expresiones aritméticas *)

Inductive Aexp : Set :=
| N : Z -> Aexp
| V : Vname -> Aexp
| Plus : Aexp -> Aexp -> Aexp
| Prod : Aexp -> Aexp -> Aexp
| Minus : Aexp -> Aexp -> Aexp. 


(* Tipo de valores, i.e., resultados de la evaluación *)

Definition Value := Z. 

(* Tipo de estados, en este caso funciones de nombres de variables en valores *)

Definition State := Vname -> Value.


(* Función de evaluación de expresiones aritméticas *)

Fixpoint aval (a:Aexp) (s:State): Value:=
match a with
| N n =>  n 
| V x => s x
| Plus a1 a2 => (aval a1 s) + (aval a2 s)
| Prod a1 a2 => (aval a1 s) * (aval a2 s)
| Minus a1 a2 => (aval a1 s) - (aval a2 s)
end. 



(* Expresiones booleanas *)

Inductive Bexp: Set :=
| B : bool -> Bexp
| Eq : Aexp -> Aexp -> Bexp
| Lt : Aexp -> Aexp -> Bexp
| Not : Bexp -> Bexp
| And : Bexp -> Bexp -> Bexp.


(* Función de evaluación de expresiones booleanas *)

Fixpoint bval (a:Bexp) (s:State): bool:=
match a with
| B b =>  b 
| Eq a1 a2 => Zeq_bool (aval a1 s) (aval a2 s)
| Lt a1 a2 => Zlt_bool (aval a1 s) (aval a2 s)
| Not b => negb (bval b s)
| And b1 b2 => andb (bval b1 s) (bval b2 s)
end. 




(* Propiedad simple de expresiones booleanas *)

Lemma SemBexp_neg: forall (b:Bexp) (s: State), 
bval b s = true ->
bval (Not b) s = false.
Proof. 
intros.
induction b.
simpl bval.
simpl in H.
rewrite H.
simpl.
trivial.
simpl.
simpl in H.
rewrite H.
simpl.
trivial.
simpl.
simpl in H.
rewrite H.
trivial.
replace (bval (Not (Not b)) s) with (negb (bval (Not b) s)).
rewrite H.
trivial.
simpl.
trivial.
simpl.
simpl in H.
rewrite H.
trivial.
Qed.




(* Declaraciones sin implementación para manejar conjuntos de variables *)

Hypothesis VarSet: Set.

(* Funciones de manejo de conjuntos de variables *)
 
Variable empty : VarSet. 
Variable single : Vname -> VarSet.
Variable union : VarSet -> VarSet -> VarSet. 
Variable elemvs: Vname -> VarSet -> Prop.

(* Propiedades de la función elemvs *)

Variable elem_single: forall (x:Vname), elemvs x (single x). 

Variable elem_union_R: forall (x:Vname) (e e':VarSet), 
elemvs x e -> elemvs x (union e e').

Variable elem_union_L: forall (x:Vname) (e e':VarSet), 
elemvs x e -> elemvs x (union e' e).


(* Definición del conjunto de variables de una expresión aritmética *)

Fixpoint VAexp (a:Aexp) : VarSet :=
match a with
| N n => empty
| V v => single v
| Plus a1 a2 => union (VAexp a1) (VAexp a2)
| Prod a1 a2 => union (VAexp a1) (VAexp a2)
| Minus a1 a2 => union (VAexp a1)  (VAexp a2)
end. 


(* Lema de coincidencia para expresiones aritméticas *)

Lemma coinc_Aexp: 
forall (a: Aexp) (s s':State), 
(forall x:Vname, elemvs x (VAexp a) -> s x = s' x) ->
aval a s = aval a s'. 
Proof. 
intros.
induction a.
simpl.
trivial. 
simpl.
apply H.
simpl.
apply elem_single.
simpl.
cut (aval a1 s = aval a1 s').
intros.
cut (aval a2 s = aval a2 s').
intros.
rewrite H0.
rewrite H1.
trivial.
apply IHa2.
intros.
apply H.
simpl.
apply elem_union_L.
trivial.
Admitted.
(* El resto de la prueba es rutinaria, terminenla *)


(* Definir la función que devuelve las variables de una expresión booleana *)

Fixpoint VBexp (b:Bexp) : VarSet := admit.


(* Lema de coincidencia para expresiones booleanas, ejercicio *)

Lemma coinc_Bexp: 
forall (b: Bexp) (s s':State), 
(forall x:Vname, elemvs x (VBexp b) -> s x = s' x) ->
bval b s = bval b s'. 
Proof. 
Admitted.


(* Sustitución en expresiones aritméticas *)

Fixpoint sustae (a:Aexp) (x:Vname) (e: Aexp): Aexp :=
match a with
| N n => N n 
| V y => if string_dec x y then e else V y
| Plus a1 a2 => Plus (sustae a1 x e) (sustae a2 x e)
| Prod a1 a2 => Prod (sustae a1 x e) (sustae a2 x e)
| Minus a1 a2 => Minus (sustae a1 x e) (sustae a2 x e)
end. 

(* Ejemplo de sustitución *)

Eval simpl in (sustae (Plus (V "x") (N 1)) "x" (N 3)).

Eval simpl in 
  (sustae (Plus (V "x") (Prod (V "y") (V "x"))) "x" (Minus (V "y") (N 5))). 


(* Sustitución en expresiones booleanas, ejercicio *)

Fixpoint sustbe (b:Bexp) (x:Vname) (e: Aexp): Bexp := admit. 



(* Función de actualización de estados *)

Definition update (s: State) (y:Vname) (v:Value): State := 
fun (x:Vname) => if string_dec x y then v else s x. 


(* Lemas necesarios posteriormente, usar string_dec para probarlos*)

Check string_dec.

Lemma upd_eq: forall (s: State) (y:Vname) (v:Value), update s y v y = v.
Admitted.



Lemma upd_neq: forall (s: State) (y x:Vname) (v:Value), y <> x -> update s y v x = s x.
Admitted.


(* Lema de sustitución para expresiones aritméticas, ejercicio *)


Lemma sust_ae: forall a y e s, 
aval (sustae a y e) s = aval a (update s y (aval e s)). 
Admitted.


(* Lema de sustitución para expresiones aritméticas, ejercicio *)


Lemma sust_be: forall b y e s, 
bval (sustbe b y e) s = bval b (update s y (aval e s)). 
Admitted.









