(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 15,  Semántica Axiomática para el lenguaje WHILE (Lógica de Hoare) *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import Setoid.

(* Esta definición es para poder declarar funciones sin dar su definición *)
Definition admit {T: Type} : T. Admitted.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Open Scope type_scope.  
Open Scope Z_scope.


(* Cerradura transitiva *)

Inductive Tcl {A:Type} (R:A -> A -> Prop): A -> A -> Prop :=
  | TCr : forall (x:A), Tcl R x x 
  | Tct : forall (x y z:A), R x y -> Tcl R y z -> Tcl R x z.

Check Tcl_ind.


Lemma Tcltr: forall (A:Type) (R:A -> A -> Prop), forall (x y z:A), Tcl R x y -> 
Tcl R y z -> Tcl R x z.
Admitted.


Lemma rinTclr: forall (A:Type) (R:A -> A -> Prop), forall (x y:A), R x y -> Tcl R x y.
Admitted.

Lemma Tclcr: forall (A:Type) (R:A -> A -> Prop), forall (x y z:A), Tcl R x y -> R y z -> Tcl R x z.
Admitted.


(* Tipo de valores, i.e., resultados de la evaluación *)
Definition Value := Z. 

(* Tipo de nombres de variables *)

Definition Vname := string.
Definition State := Vname -> Value.
Definition update (s: State) (y:Vname) (v:Value): State := 
fun (x:Vname) => if string_dec x y then v else s x. 

Inductive Aexp : Set :=
| N : Z -> Aexp
| V : Vname -> Aexp
| Plus : Aexp -> Aexp -> Aexp
| Prod : Aexp -> Aexp -> Aexp
| Minus : Aexp -> Aexp -> Aexp. 







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




(* Semántica axiomática, lógica de Hoare *)

Definition Assertion := State -> Prop.


Definition Istrue (b:Bexp):Assertion := 
 fun s:State => bval b s = true.

Definition Isfalse (b:Bexp):Assertion :=
 fun s:State => bval b s = false.


Inductive AndAss (P Q:Assertion) (s:State): Prop :=
 Conjass : P s -> Q s -> AndAss P Q s.

Definition ImplAss (P Q:Assertion): Prop :=
 forall s:State, P s -> Q s.


Definition assupd (x:Vname) (a:Aexp) (P:Assertion):Assertion :=
 fun s:State => P (update s x (aval a s)).



Inductive AxSemH: Assertion -> Com -> Assertion -> Prop :=
 |AxS_Skip: forall P:Assertion, AxSemH P Skip P
 |AxS_Assg: forall (P:Assertion) (x:Vname) (a:Aexp),
            AxSemH (assupd x a P) (Assg x a) P
 |AxS_Seq: forall (P Q R:Assertion) (c1 c2:Com),
            AxSemH P c1 R -> AxSemH R c2 Q -> AxSemH P (Seq c1 c2) Q
 |AxS_If: forall (P Q:Assertion) (b:Bexp) (c1 c2:Com),
             AxSemH (AndAss P (Istrue b)) c1 Q ->
             AxSemH (AndAss P (Isfalse b)) c2 Q -> AxSemH P (IfC b c1 c2) Q
 |AxS_While: forall (P:Assertion) (b:Bexp) (c:Com), 
              AxSemH (AndAss P (Istrue b)) c P ->
               AxSemH P (While b c) (AndAss P (Isfalse b))
 |AxS_Cons: forall (P P' Q Q':Assertion) (c:Com), 
              ImplAss P P' -> AxSemH P' c Q' ->
              ImplAss Q' Q -> AxSemH P c Q.


Notation " {{ P }} c {{ Q }}" := (AxSemH P c Q) (at level 30). 


Variable Q: State -> Prop.
Variable x y z i: Vname.

Lemma ej1 : {{ assupd x (N 5) Q }}  (x ::= N 5) {{ Q }}.
Proof.
intros.
constructor.
Qed.


Definition Pre:= fun s:State => s y = 1.

Lemma ej2 : {{ assupd x (N 1) ( assupd y (V x) Pre) }} x ::= N 1 ;; y ::= V x {{ Pre }}.
Proof.
intros.
eapply AxS_Seq.
apply AxS_Assg.
constructor.
Qed.





Definition HoareTcorr (P:Assertion) (c:Com) (Q:Assertion) := forall (s t:State), P s -> << c , s >> ==> t -> Q t.




Theorem HoareLsound : forall (P Q:Assertion) (c:Com), {{ P }} c {{ Q }} -> HoareTcorr P c Q.

Proof.
intros P Q c T.
induction T.
unfold HoareTcorr.
intros.
inversion H0.
rewrite <- H3.
trivial.

unfold HoareTcorr.
intros.
inversion H0.
exact H.

unfold HoareTcorr.
intros.
inversion H0.
apply (IHT2 s2) .
apply (IHT1 s).
trivial.
trivial.
trivial.


unfold HoareTcorr.
intros.
inversion H0.
clear H1 H2 H4 H3 H5.
clear b0 s0 t0 c0 c3.
apply (IHT1 s).
constructor.
trivial.
exact H6.
trivial.
clear H1 H2 H4 H3 H5.
clear b0 s0 t0 c0 c3.
apply (IHT2 s).
constructor.
trivial.
exact H6.
trivial.

(*
unfold HoareTcorr.
intros.
inversion H0.
clear H1 H3 H2.
clear b0 c0 s0.
constructor.
rewrite <- H4.
trivial.
exact H5.




clear H1 H2 H5 H6.
clear b0 s1 c0 s3.




Let AndAsswhile (c : Com) (s s' : State) (P : Assertion) :=
  match c with
  | While b c1 =>
      ( forall (s1 s2 : State), << c1 , s1 >> ==>  s2 -> AndAss P (Istrue b) s1 -> P s2 ) ->
      P s -> AndAss P (Isfalse b) s'
  | _ => True
  end.
*)


unfold HoareTcorr.
intros.

Let AndAsswhile (c : Com) (s s' : State) (P : Assertion) :=
  match c with
  | While b c1 => HoareTcorr (AndAss P (Istrue b)) c1 P -> P s -> AndAss P (Isfalse b) s'
  | _ => True
  end.
generalize IHT H.

change (AndAsswhile (While b c) s t P).


induction H0.
simpl.
trivial.
simpl.
trivial.
simpl.
trivial.
simpl.
trivial.
simpl.
trivial.

simpl.
intros.
constructor.
trivial.
exact H0.

simpl.
intros.
unfold AndAsswhile in IHBSSem2.
assert (P s2).

unfold HoareTcorr in H1.
apply (H1 s1 s2).
constructor.
trivial.
exact H0.
trivial.

apply IHBSSem2.
trivial.
exact H1.
trivial.

unfold HoareTcorr.
intros.
apply H0.
apply (IHT s t).
apply H.
trivial.
trivial.
Qed.



(*
elim H0 ; simpl; trivial.

intros.
constructor.
trivial.
trivial.
intros.
apply H5.
exact H6.

unfold HoareTcorr in H6.

apply (H6 s1 s2).  
constructor.
trivial.
exact H1.
trivial.

unfold HoareTcorr.
intros.
apply H0.
apply (IHT s t).
apply H.
trivial.
trivial.
Qed.

*)
















