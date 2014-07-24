(** * Lenguaje IMP/WHILE 1: expresiones aritméticas y booleanas *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope string_scope.
Definition admit {T: Type} : T. Admitted.

(** Notaciones usuales para listas, así podemos escribir x::l para construir listas, [] como sinónimo de la lista vacia y [x, .. , y] para construir listas *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Eval compute in 5::[1,2,3,4].

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

Eval compute in  2 + 2 + 4 = 9.


Lemma SemBexp_neg: forall (b:Bexp) (s: State), 
bval b s = true ->
bval (Not b) s = false.
Proof. 
destruct b;intros;simpl;simpl in H;rewrite H;reflexivity.
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

Inductive Com: Set :=
| Skip : Com
| Assg : Vname -> Aexp -> Com
| Seq : Com -> Com -> Com
| IfC :  Bexp -> Com -> Com -> Com
| While : Bexp -> Com -> Com.


Notation "x ::= a" := (Assg x a) (at level 20).
Notation "c ;; c'" := (Seq c c') (at level 30).


Inductive BSSem:Com -> State -> State -> Prop :=
 |BS_Assg : forall (x:Vname) (a:Aexp) (s:State),
                 BSSem (Assg x a) s (update s x (aval a s))
 |BS_Skip : forall s:State, BSSem Skip s s
 |BS_Seq : forall (c1:Com) (s1 s2:State), 
                  BSSem c1 s1 s2 -> 
                  forall (c2:Com) (s3:State) , BSSem c2 s2 s3 -> 
                  BSSem (Seq c1 c2) s1 s3
 |BS_IfT: forall (b:Bexp) (s:State), bval b s = true -> 
           forall (t:State),
             forall (c1 c2:Com), BSSem c1 s t -> BSSem (IfC b c1 c2) s t
 |BS_IfF: forall (b:Bexp) (s:State), bval b s = false -> 
           forall (t:State),
             forall (c1 c2:Com), BSSem c2 s t -> BSSem (IfC b c1 c2) s t
 |BS_WhlF: forall (b:Bexp) (c:Com) (s:State), bval b s = false ->
               BSSem (While b c) s s
 |BS_WhlT: forall (b:Bexp) (s1:State), bval b s1 = false ->
                    forall (c:Com) (s2:State), BSSem c s1 s2 ->
                       forall (s3:State), BSSem (While b c) s2 s3 ->
                          BSSem (While b c) s1 s3. 


Notation " ( c , s ) ==> t" := (BSSem c s t) (at level 30).

               
(* Seq (Assg "x" (N 5)) (Assg "y" (V "x")). *)

Definition p1 :=  "x" ::= N 5 ;; "y" ::= V "x".


Lemma ejp1: forall (s:State), exists t:State, ( p1 , s ) ==> t.
Proof.
intros.
eexists.
unfold p1.
eapply BS_Seq.
eapply BS_Assg.
eapply BS_Assg.
Qed.

Print ejp1.


Definition bsequiv (c1 c2:Com):Prop := forall (s t:State), 
                                       ( c1,s ) ==> t <-> ( c2,s ) ==> t.

Check bsequiv.                 

Notation "c ~~ d" := (bsequiv c d) (at level 40).



Lemma equiv_if_A: forall (b:Bexp) (c:Com), IfC b c c ~~ c.
Proof.
intros.
unfold bsequiv.
intros.
split.
intros.
inversion H.
trivial.
trivial.
intros.
case (bool_dec (bval b s) true).
intros.
apply BS_IfT.
trivial.
trivial.
intros.
apply BS_IfF.
apply not_true_is_false.
trivial.
trivial.
Qed.



Lemma equiv_if_B: forall (b:Bexp) (c1 c2:Com), IfC b c1 c2 ~~ IfC (Not b) c2 c1.
Proof.
intros.
unfold bsequiv.
intros.
split.
intros.
inversion H.
apply BS_IfF.
simpl.
rewrite H5.
simpl.
trivial.
trivial.
apply BS_IfT.
simpl.
rewrite H5.
simpl.
trivial.
trivial.
intros.
case (bool_dec (bval b s)  true).
intros.
apply BS_IfT.
trivial.
inversion H.
simpl in H5.
rewrite e in H5.
exfalso.
intuition.
trivial.
intros.
apply BS_IfF.
apply not_true_is_false.
trivial.
inversion H.
trivial.
exfalso.
simpl in H5.
apply n.
apply negb_false_iff.
trivial.
Qed.


Lemma equiv_unfold_while: forall (b:Bexp) (c:Com), 
                           While b c ~~ IfC b (c ;; (While b c)) Skip.
Admitted.


Theorem cong_while: forall (b:Bexp) (c c':Com) (s t:State), 
                      ( While b c , s ) ==> t  -> c ~~ c' -> ( While b c' , s ) ==> t.
Admitted. 


Theorem determ_Imp: forall (c:Com) (s t t':State),
                      (c , s) ==> t -> (c , s) ==> t' -> t = t'.
Admitted.
