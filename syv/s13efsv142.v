(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 13,  Lenguaje IMP/WHILE 1: semántica de paso pequeño, equivalencia con la semántica de paso grande *)


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




(* Comandos *)

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
 |BS_WhlT: forall (b:Bexp) (s1:State), bval b s1 = true ->
                    forall (c:Com) (s2:State), BSSem c s1 s2 ->
                       forall (s3:State), BSSem (While b c) s2 s3 ->
                          BSSem (While b c) s1 s3. 


Notation " << c , s >> ==> t" := (BSSem c s t) (at level 30).

               
(* Seq (Assg "x" (N 5)) (Assg "y" (V "x")). *)

Definition p1 :=  "x" ::= N 5 ;; "y" ::= V "x".


Lemma ejp1: forall (s:State), exists t:State, << p1 , s >> ==> t.
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
                                       << c1,s >> ==> t <-> << c2,s >> ==> t.

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
                      << While b c , s >> ==> t  -> c ~~ c' -> << While b c' , s >> ==> t.
Admitted. 


Theorem determ_Imp: forall (c:Com) (s t t':State),
                      << c , s >> ==> t -> << c , s >> ==> t' -> t = t'.
Admitted.





Inductive SSSem: Com * State -> Com * State -> Prop :=
 |SS_Assg : forall (x:Vname) (a:Aexp) (s:State),
                 SSSem (Assg x a, s)  (Skip, update s x (aval a s))
 |SS_SeqL : forall (c1 c1':Com) (s s':State), 
                  SSSem (c1,s) (c1',s') -> 
                  forall (c2:Com), SSSem (Seq c1 c2, s) (Seq c1' c2, s') 
 |SS_SeqR : forall (c2:Com) (s:State), SSSem (Seq Skip c2,s) (c2,s)

 |SS_IfT: forall (b:Bexp) (s:State), bval b s = true -> 
                  forall (c1 c2:Com), SSSem (IfC b c1 c2,s) (c1,s)
 |SS_IfF: forall (b:Bexp) (s:State), bval b s = false -> 
                  forall (c1 c2:Com), SSSem (IfC b c1 c2,s) (c2,s)
 |SS_Whl: forall (b:Bexp) (c:Com) (s:State), 
               SSSem (While b c, s) (IfC b (Seq c (While b c)) Skip,s).



Notation " '<<' c , s '>>'  --->  '<<' c' , s' '>>'":= (SSSem (c,s) (c',s')) (at level 30).




(* Definicion de la cerradura transitiva *)

Inductive Tcl {A:Type} (R:A -> A -> Prop): A -> A -> Prop :=
  | TCr : forall (x:A), Tcl R x x 
  | Tct : forall (x y z:A), R x y -> Tcl R y z -> Tcl R x z.



Check Tcl_ind.


Lemma Tcltr: forall (A:Type) (R:A -> A -> Prop), forall (x y z:A), Tcl R x y -> Tcl R y z -> Tcl R x z.
Proof.
intros.
induction H.
trivial.
assert (Tcl R y z).
exact (IHTcl H0).
eapply Tct.
eexact H.
trivial.
Qed.


Lemma rinTclr: forall (A:Type) (R:A -> A -> Prop), forall (x y:A), R x y -> Tcl R x y.
Proof.
intros.
eapply Tct.
eexact H.
apply TCr.
Qed.


Lemma Tclcr: forall (A:Type) (R:A -> A -> Prop), forall (x y z:A), Tcl R x y -> R y z -> Tcl R x z.
Admitted.


Definition SSSemStar := Tcl SSSem.




Notation " '<<' c , s '>>'  --->*  '<<' c' , s' '>>'":= (SSSemStar (c,s) (c',s')) (at level 30).



Lemma Xsss_seq: forall (c1 c1':Com) (s s':State), << c1 , s >> --->*  << c1',s'>> -> forall (c2:Com), << c1;;c2,s >> --->* << c1';;c2,s' >>.
Proof.
intros.
induction H.
admit.

trivial.
Qed.



Lemma sss_seqG: forall (cs1 cs1': Com*State), SSSemStar cs1 cs1' -> forall (c2:Com), 
                  SSSemStar (pair (fst cs1 ;; c2) (snd cs1))  (pair (fst cs1' ;; c2) (snd cs1')).
Proof.
intros cs1 cs1' H.
induction H.
constructor.
intros.
cut (SSSem (fst x;; c2, snd x) (fst y;;c2,snd y)).
intros.
eapply Tct.
eexact H1.
apply IHTcl.
replace x with (fst x,snd x) in H.
replace y with (fst y,snd y) in H.
apply SS_SeqL.
trivial.
symmetry.
apply surjective_pairing.
symmetry.
apply surjective_pairing.
Qed.

Print pair.


Lemma sss_seq: forall (c1 c1':Com) (s s':State), << c1 , s >> --->*  << c1',s'>> -> forall (c2:Com), << c1;;c2,s >> --->* << c1';;c2,s' >>.
Admitted.


Lemma seqskip: forall (c1:Com) (s1 s2:State), SSSemStar (c1,s1) (Skip,s2) ->
                 forall (c2:Com) (s3:State), SSSemStar (c2,s2) (Skip,s3) -> SSSemStar (c1 ;; c2, s1) (Skip,s3).
Proof.
intros.
inversion H.
eapply  Tct.
eapply SS_SeqR.
trivial.
cut (<< c1 ;; c2, s1 >> --->* << Skip ;; c2, s2 >>).
intros.
assert ( << Skip ;; c2, s2 >> ---> << c2,s2 >>).
apply SS_SeqR.
assert ( << c1 ;; c2, s1 >> --->* << c2,s2 >>). 
eapply Tclcr.
eexact H5.
exact H6.
eapply Tcltr.
eexact H7.
exact H0.
apply sss_seq.
exact H.
Qed.



Lemma sscbs1: forall (c c':Com) (s s':State), << c,s >> ---> << c',s' >> -> forall (t:State), << c',s' >> ==> t -> << c,s >> ==> t.
Admitted.


Lemma sscbs: forall (c c':Com) (s s':State), << c,s >> --->* << c',s' >> -> forall (t:State), << c',s' >> ==> t -> << c,s >> ==> t.
Proof.
intros c c' s s' H.
induction H.
Admitted.



Theorem ss_implies_bs: forall (c:Com) (s t:State), << c,s >> ==> t 
                          ->  << c,s >> --->* << Skip, t >>.
Proof.
intros.
induction H.
apply rinTclr.
constructor.
constructor.
eapply seqskip.
eexact IHBSSem1.
trivial.
eapply Tct.
eapply SS_IfT.
trivial.
trivial.
admit.
eapply Tct.
eapply SS_Whl.
apply rinTclr.
constructor.
trivial.
eapply Tct.
constructor.
eapply Tct.
constructor.
trivial.
eapply seqskip.
eexact IHBSSem1.
eexact IHBSSem2.
Qed.


Theorem bs_implies_ss_G: forall (cs st:Com*State),  SSSemStar cs st -> fst st = Skip -> 
  BSSem (fst cs) (snd cs) (snd st).
Proof.
intros.
induction H.
rewrite H0.
constructor.
assert ( << fst y, snd y >> ==> snd z).
apply IHTcl.
trivial.
replace x with (fst x,snd x) in H.
replace y with (fst y,snd y) in H.
replace y with (fst y,snd y) in H1.
replace z with (fst z,snd z) in H1.
eapply sscbs1.
eexact H.
exact H2.
symmetry.
apply surjective_pairing.
symmetry.
apply surjective_pairing.
symmetry.
apply surjective_pairing.
symmetry.
apply surjective_pairing.
Qed.

Theorem bs_implies_ss: forall (c:Com) (s t:State),  << c,s >> --->* << Skip, t >> 
                           -> << c,s >> ==> t.
Admitted.
