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
(*   ******************************************************* *)
(* end hide *)

(**  ** Problema 1 *)
(**
La semántica de las expresiones aritméticas está dada por la función $\mathcal{A}$. También podemos tomar un enfoque operacional y definir una semántica natural para expresiones aritméticas.
Deberán existir 2 configuraciones:
 - $\sigma$ Denotando que a debe evaluarse en el estado $\sigma$
 - z Denotando un valor final. (elementos de $\mathbb{Z}$)

La relación de transición $\Rightarrow_{AExp}$ tendrá la forma :

$\langle a, \sigma \rangle \Rightarrow_{AExp} z$

Por ejemplo:

 - $\langle  n, \sigma \rangle \Rightarrow_{AExp} n $
 - $\langle x, \sigma \rangle \Rightarrow_{AExp} \sigma x$
 - $\frac{\langle a_1 , \sigma \rangle \Rightarrow_{AExp} z_1 \>\> \langle a_1 , \sigma \rangle \Rightarrow_{AExp} z_2}{ \langle a_1 + a_2 , \sigma \rangle \Rightarrow_{AExp}(z_1+z_2) }$
*)

(** *** Complete la definición del sistema de transiciones. *)

(**
 - $\frac{\langle a_1 , \sigma \rangle \Rightarrow_{AExp} z_1 \>\> \langle a_1 , \sigma \rangle \Rightarrow_{AExp} z_2}{ \langle a_1 * a_2 , \sigma \rangle \Rightarrow_{AExp}(z_1 * z_2) }$
 - $\frac{\langle a_1 , \sigma \rangle \Rightarrow_{AExp} z_1 \>\> \langle a_1 , \sigma \rangle \Rightarrow_{AExp} z_2}{ \langle a_1 - a_2 , \sigma \rangle \Rightarrow_{AExp}(z_1 - z_2) }$
*)
(** *** Demuestre que este enfoque es equivalente a la función $\mathcal{A}$.*)


(* Esta es la definición que vimos en clase como una funcion recursiva de evaluación de expresiones aritméticas *)
(* begin hide *)
Definition Value := Z.
Definition State := Vname -> Value.

Inductive Aexp : Set :=
| N : Z -> Aexp
| V : Vname -> Aexp
| Plus : Aexp -> Aexp -> Aexp
| Prod : Aexp -> Aexp -> Aexp
| Minus : Aexp -> Aexp -> Aexp. 

Fixpoint aval (a:Aexp) (s:State): Value:=
match a with
| N n =>  n 
| V x => s x
| Plus a1 a2 => (aval a1 s) + (aval a2 s)
| Prod a1 a2 => (aval a1 s) * (aval a2 s)
| Minus a1 a2 => (aval a1 s) - (aval a2 s)
end. 

Hypothesis VarSet: Set.
Variable empty : VarSet. 
Variable single : Vname -> VarSet.
Variable union : VarSet -> VarSet -> VarSet. 
Variable elemvs: Vname -> VarSet -> Prop.
Variable elem_single: forall (x:Vname), elemvs x (single x). 
Variable elem_union_R: forall (x:Vname) (e e':VarSet), 
                         elemvs x e -> elemvs x (union e e').
Variable elem_union_L: forall (x:Vname) (e e':VarSet), 
                         elemvs x e -> elemvs x (union e' e).
Definition update (s: State) (y:Vname) (v:Value): State := 
  fun (x:Vname) => if string_dec x y then v else s x. 

Fixpoint VAexp (a:Aexp) : VarSet :=
match a with
| N n => empty
| V v => single v
| Plus a1 a2 => union (VAexp a1) (VAexp a2)
| Prod a1 a2 => union (VAexp a1) (VAexp a2)
| Minus a1 a2 => union (VAexp a1)  (VAexp a2)
end.
(* end hide *)

(** Definamos la operación de evaluación especificada. *)

Inductive AEval_op : Aexp -> State -> Value -> Prop :=
  | Aop_n  : forall (s: State) (z: Value), AEval_op (N z) s z
  | Aop_v  : forall (s: State) (x :Vname), AEval_op (V x) s (s x)
  | Aop_sum : forall (s: State) (e1 e2: Aexp) (n1 n2: Value),
      AEval_op e1 s n1 -> AEval_op e2 s n2 ->
      AEval_op (Plus e1 e2) s (n1 + n2)
  | Aop_sub: forall (s: State) (e1 e2: Aexp) (n1 n2: Value),
      AEval_op e1 s n1 -> AEval_op e2 s n2 ->
      AEval_op (Minus e1 e2) s (n1 - n2)
  | Aop_mul : forall (s: State) (e1 e2: Aexp) (n1 n2: Value),
      AEval_op e1 s n1 -> AEval_op e2 s n2 ->
      AEval_op (Prod e1 e2) s (n1 * n2).

(** 

Y finalmentente el resultado solicitado, que es demostrar la equivalencia 

*)
 
Theorem  equivalencia_op: forall (e: Aexp) (s: State) (n :Value),
  AEval_op e s n <-> aval e s = n.
Proof.
  split.
  intros.
  induction H; 
    try(reflexivity);
    try(simpl;rewrite IHAEval_op1, IHAEval_op2;reflexivity).
  generalize dependent n.
  generalize dependent s.
  induction e;
    try(intros;rewrite <- H;simpl;try apply Aop_n; try apply Aop_v;simpl).
  apply Aop_sum. apply IHe1. reflexivity. apply IHe2. reflexivity.
  apply Aop_mul. apply IHe1. reflexivity. apply IHe2. reflexivity.
  apply Aop_sub. apply IHe1. reflexivity. apply IHe2. reflexivity.
Qed.

(**  ** Problema 2 *)
(** 
Extendemos la definición del while con el comando.
<<
repeat c until b
>>
Para que la secuencia c se repita hasta que b sea verdadero.
*)

(** *** Extienda la semántica de paso grande con repeat. *)

(* begin hide *)
(* Necesitamos también la evaluación de las expresiones booleanas para la semántica operacional *)

Inductive Bexp: Set :=
| B : bool -> Bexp
| Eq : Aexp -> Aexp -> Bexp
| Lt : Aexp -> Aexp -> Bexp
| Not : Bexp -> Bexp
| And : Bexp -> Bexp -> Bexp.

Fixpoint bval (a:Bexp) (s:State): bool:=
match a with
| B b =>  b 
| Eq a1 a2 => Zeq_bool (aval a1 s) (aval a2 s)
| Lt a1 a2 => Zlt_bool (aval a1 s) (aval a2 s)
| Not b => negb (bval b s)
| And b1 b2 => andb (bval b1 s) (bval b2 s)
end. 

Check eq_ind.

Theorem false_not_true: true = false -> False. Admitted.
(* end hide *)

(** Agregamos el comando Repeat al lenguage que desarrollamos en clase *)

Inductive Com: Set :=
| Skip : Com
| Assg : Vname -> Aexp -> Com
| Seq : Com -> Com -> Com
| IfC :  Bexp -> Com -> Com -> Com
| While : Bexp -> Com -> Com
| Repeat : Com -> Bexp -> Com.


(** Y la semantica de paso grande queda entonces definida de la siguiente manera: *)

Inductive BSSem:Com -> State -> State -> Prop :=
|BS_Assg : forall (x:Vname) (a:Aexp) (s:State),
             BSSem (Assg x a) s (update s x (aval a s))
|BS_Skip : forall s:State, BSSem Skip s s
|BS_Seq : forall (c1:Com) (s1 s2:State), 
            BSSem c1 s1 s2 -> 
            forall (c2:Com) (s3:State) , 
              BSSem c2 s2 s3 -> 
              BSSem (Seq c1 c2) s1 s3
 |BS_IfT: forall (b:Bexp) (s:State), 
            bval b s = true -> 
            forall (t:State),forall (c1 c2:Com), 
              BSSem c1 s t -> BSSem (IfC b c1 c2) s t
 |BS_IfF: forall (b:Bexp) (s:State), 
            bval b s = false -> 
            forall (t:State), forall (c1 c2:Com), 
              BSSem c2 s t -> BSSem (IfC b c1 c2) s t
 |BS_WhlF: forall (b:Bexp) (c:Com) (s:State), 
             bval b s = false ->
             BSSem (While b c) s s
 |BS_WhlT: forall (b:Bexp) (s1:State), 
             bval b s1 = true ->
             forall (c:Com) (s2:State),
               BSSem c s1 s2 ->
               forall (s3:State), 
                 BSSem (While b c) s2 s3 ->
                 BSSem (While b c) s1 s3
 |BS_RepT: forall (c:Com) (b:Bexp) (s s1 :State), 
             BSSem c s s1 ->
             bval b s1 = true ->
             BSSem (Repeat c b) s s1
 |BS_RepF: forall (c:Com) (b:Bexp) (s s1 :State), 
             BSSem c s s1 ->
             bval b s1 = false ->
               forall (t:State), 
                 BSSem (Repeat c b) s1 t ->
                 BSSem (Repeat c b) s t.

Notation " << c , s >> ==> t" := (BSSem c s t) (at level 30).
Definition bsequiv (c1 c2:Com):Prop := 
  forall (s t:State),<< c1,s >> ==> t <-> << c2,s >> ==> t.
 Notation "c ~~ d" := (bsequiv c d) (at level 40). 

Lemma const_bool: forall (s': State) (b: bool ), bval (B b) s' = b.
Proof. intros. reflexivity. Qed.
  
(** 
Un lema que prueba el caso trivial cuando until es la constante true, que debería de aplicar el comando una vez y salir inmediatamente. *)

Lemma repeat_with_true: 
  forall (c: Com) (s: State), (Repeat c (B true)) ~~ c.
Proof.
  intros. unfold bsequiv. intros. split. 
  intros. inversion H. assumption.
  rewrite const_bool in H3.
  exfalso. apply false_not_true. assumption. 
  intros. apply BS_RepT with (c:=c) (s:=s0) (b:=B true) (s1:=t).  
  assumption. reflexivity.
  Qed.

(**  *** Extienda la semántica de paso pequeño con repeat. *)


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
               SSSem (While b c, s) (IfC b (Seq c (While b c)) Skip,s)
 |SS_Repeat: forall (b:Bexp) (c:Com) (s :State),
               SSSem (Repeat c b, s) (Seq c (IfC b Skip (Repeat c b)),s ).

(** **** Extienda la prueba de equivalencias de las dos semánticas con el caso repeat *)
(** (puede admitir todos los otros casos en el script correspondiente) *)

(* begin hide *)
(*  *************************************************************
    pruebas y lemas vistos en clase, que son útiles en la prueba, 
    por brevedad todos admitidos. 
    ************************************************************* *)
Inductive Tcl {A:Type} (R:A -> A -> Prop): A -> A -> Prop :=
  | TCr : forall (x:A), Tcl R x x 
  | Tct : forall (x y z:A), R x y -> Tcl R y z -> Tcl R x z.
Definition SSSemStar := Tcl SSSem.
Notation "x ::= a" := (Assg x a) (at level 20).
Notation "c ;; c'" := (Seq c c') (at level 30).
Notation " '<<' c , s '>>'  --->  '<<' c' , s' '>>'":= (SSSem (c,s) (c',s')) (at level 30).
Notation " '<<' c , s '>>'  --->*  '<<' c' , s' '>>'":= (SSSemStar (c,s) (c',s')) (at level 30).
Lemma determ_Imp: forall (c:Com) (s t t':State),  << c , s >> ==> t -> << c , s >> ==> t' -> t = t'. Admitted.
Lemma sscbs1: forall (c c':Com) (s s':State), << c,s >> ---> << c',s' >> -> forall (t:State), << c',s' >> ==> t -> << c,s >> ==> t. Admitted.
Lemma sscbs: forall (c c':Com) (s s':State), << c,s >> --->* << c',s' >> -> forall (t:State), << c',s' >> ==> t -> << c,s >> ==> t. Admitted.
Lemma rinTclr: forall (A:Type) (R:A -> A -> Prop), forall (x y:A), R x y -> Tcl R x y. Admitted.
Lemma Tclcr: forall (A:Type) (R:A -> A -> Prop), forall (x y z:A), Tcl R x y -> R y z -> Tcl R x z. Admitted.
Lemma Tcltr: forall (A:Type) (R:A -> A -> Prop), forall (x y z:A), Tcl R x y -> Tcl R y z -> Tcl R x z. Admitted.
Lemma sss_seq: forall (c1 c1':Com) (s s':State), << c1 , s >> --->*  << c1',s'>> -> forall (c2:Com), << c1;;c2,s >> --->* << c1';;c2,s' >>. Admitted.
Lemma seqskip: forall (c1:Com) (s1 s2:State), SSSemStar (c1,s1) (Skip,s2) ->
                 forall (c2:Com) (s3:State), SSSemStar (c2,s2) (Skip,s3) -> SSSemStar (c1 ;; c2, s1) (Skip,s3). Admitted.
(*  ************************************************************* *)
(* end hide*)

Theorem ss_implies_bs: forall (c:Com) (s t:State), << c,s >> ==> t 
                          ->  << c,s >> --->* << Skip, t >>.
Proof.
intros.
induction H.

(** // Casos Assign, Skip, Seq. If true, If false, While false, While true. *)

admit. admit. admit. admit. admit. admit. admit. 
(** // Caso Repeat: *)

apply Tct with (y:=(Seq c (IfC b Skip (Repeat c b)),s)).
apply SS_Repeat.
eapply seqskip.
eexact IHBSSem.
apply rinTclr.
eapply SS_IfT.
assumption.
eapply Tct with (y:=(Seq c (IfC b Skip (Repeat c b)),s)).
apply SS_Repeat.
eapply seqskip.
eexact IHBSSem1.
assert ( << IfC b Skip (Repeat c b), s1 >>  --->  << Repeat c b ,s1 >> ).
apply SS_IfF.
assumption.
apply Tcltr with (x:= (IfC b Skip (Repeat c b), s1) ) (y:= ((Repeat c b), s1)).
apply rinTclr.
assumption.
assumption.
Qed.
