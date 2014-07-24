(**  * Tarea 3 Fabián Romero  *)

(* begin hide *)
(*
Comando de emacs previo a la primera compilación. TODO makefile
(let* 
    ((filename (file-name-sans-extension (file-name-nondirectory buffer-file-name)))
    (command (concat "coqdoc " filename ".v --latex --utf8 --no-externals -o " filename ".tex && pdflatex  " filename ".tex")))
    (setq compile-command command ))

*)
(*   ******************************************************* *)
(*   Bibliotecas, definiciones comúnues y preambulo habitual *)
(*   ******************************************************* *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZArith.
Open Scope Z_scope.
Open Scope string_scope.
Definition admit {T: Type} : T. Admitted.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Definition Vname := string.
Definition Value := Z.
Definition State := Vname -> Value.
Inductive Aexp : Set :=
| N : Z -> Aexp
| V : Vname -> Aexp
| Plus : Aexp -> Aexp -> Aexp
| Prod : Aexp -> Aexp -> Aexp
| Minus : Aexp -> Aexp -> Aexp. 
Inductive Bexp: Set :=
| B : bool -> Bexp
| Eq : Aexp -> Aexp -> Bexp
| Lt : Aexp -> Aexp -> Bexp
| Not : Bexp -> Bexp
| And : Bexp -> Bexp -> Bexp.
Fixpoint aval (a:Aexp) (s:State): Value:=
match a with
| N n =>  n 
| V x => s x
| Plus a1 a2 => (aval a1 s) + (aval a2 s)
| Prod a1 a2 => (aval a1 s) * (aval a2 s)
| Minus a1 a2 => (aval a1 s) - (aval a2 s)
end. 
Fixpoint bval (a:Bexp) (s:State): bool:=
match a with
| B b =>  b 
| Eq a1 a2 => Zeq_bool (aval a1 s) (aval a2 s)
| Lt a1 a2 => Zlt_bool (aval a1 s) (aval a2 s)
| Not b => negb (bval b s)
| And b1 b2 => andb (bval b1 s) (bval b2 s)
end. 
Hypothesis VarSet: Set.
Variable empty : VarSet. 
Variable single : Vname -> VarSet.
Variable union : VarSet -> VarSet -> VarSet. 
Variable elemvs: Vname -> VarSet -> Prop.
Variable elem_single: forall (x:Vname), elemvs x (single x). 
Variable elem_union_R: forall (x:Vname) (e e':VarSet), elemvs x e -> elemvs x (union e e').
Variable elem_union_L: forall (x:Vname) (e e':VarSet), elemvs x e -> elemvs x (union e' e).
Definition update (s: State) (y:Vname) (v:Value): State := fun (x:Vname) => if string_dec x y then v else s x. 
Definition Assertion := State -> Prop.
Definition Istrue (b:Bexp):Assertion :=  fun s:State => bval b s = true.
Definition Isfalse (b:Bexp):Assertion := fun s:State => bval b s = false.
Inductive AndAss (P Q:Assertion) (s:State): Prop := Conjass : P s -> Q s -> AndAss P Q s.
Definition ImplAss (P Q:Assertion): Prop := forall s:State, P s -> Q s.
Definition assupd (x:Vname) (a:Aexp) (P:Assertion):Assertion := fun s:State => P (update s x (aval a s)).
Lemma tt_True: (true = true) = True. Admitted.
(* end hide *)

(** *** Problema 3 *)
(**
Extendemos la definición del while con el comando
<<
assert b before c
>>
Tal que si b se evalúa a verdadero entonces se ejecuta c. En otro caso, la ejecución del programa completo termina.

la regla de derivación es:

 - $ \frac{\{P\>\wedge\> b\}\>c\>\{Q\}}{\{P\}\>Assert\>b\>c\>\{Q\}} $.

Así, queda definido como:
 *)

Inductive Com: Set :=
| Skip : Com
| Assg : Vname -> Aexp -> Com
| Seq : Com -> Com -> Com
| IfC :  Bexp -> Com -> Com -> Com
| While : Bexp -> Com -> Com
| Repeat : Com -> Bexp -> Com
| Assert : Bexp -> Com -> Com.

Notation "x ::= a" := (Assg x a) (at level 20).
Notation "c ;; c'" := (Seq c c') (at level 30).

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
              ImplAss P P' -> AxSemH P' c Q' -> ImplAss Q' Q -> AxSemH P c Q
 |AxS_Assert: forall (P Q:Assertion) (b:Bexp) (c:Com), 
              AxSemH (AndAss P (Istrue b)) c Q ->
               AxSemH P (Assert b c) Q.



Notation "{{ P }} c {{ Q }}" := (AxSemH P c Q) (at level 30). 

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Lemma a2 : forall (P :Assertion), assert_implies (AndAss P (Istrue (B true))) P. Admitted.

Lemma e1 : forall (P' P Q :Assertion) (c :Com),
{{ P' }} c {{ Q }} -> assert_implies P P' -> {{ P }} c {{ Q }}. Admitted.
  

Lemma ej11 : forall (s:State) (P: Assertion), {{ P }}  Assert (B true) Skip {{ P }}.
Proof.
constructor.
apply e1 with (P':=P).
constructor.
apply a2.
Qed.

(** * Pruebe las siguientes reglas derivadas de la lógica de Hoare: *)

(** ** $ \frac{P\rightarrow Q}{\{P\}\>Skip\>\{Q\}} $ *)

Lemma ej4_1 : forall (P Q: Assertion), assert_implies P Q -> {{ P }}  Skip {{ Q }}.
Proof.
intros.
apply e1 with (P':=Q) (P:=P) (c:= Skip).
constructor.
trivial.
Qed.

(** ** $ \frac{P\rightarrow Q[x/a]}{\{P\}\>x:=a\>\{Q\}} $ *)

Lemma ej4_2 : forall (P Q: Assertion) (a: Aexp) (x: Vname), assert_implies P (assupd x a Q) -> {{ P }}  (Assg x a) {{ Q }}.
Proof.
intros.
apply e1 with (P':=(assupd x a Q)) (P:=P) (c:= Assg x a).
constructor.
trivial.
Qed.

