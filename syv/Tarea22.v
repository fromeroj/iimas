
(* EspecIficación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 2, Números naturales y sus propiedades *)
(*
http://coq.inria.fr/library/Coq.Init.Datatypes.html
*)

Require Import Coq.Lists.List.


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Definition lenat:= list bool.







Inductive mnat : Set :=
  | O : mnat
  | S : mnat -> mnat.



Definition zero: mnat := O.

Print zero.

Definition one: mnat := S O.

Print one.

Definition one' := S zero.

Print one'.

Theorem oeo: one = one'.
Proof.
unfold one.
unfold one'.
unfold zero.
reflexivity.
Qed.



Definition two := (S (S O)).
Definition two' := S one.


Definition five: mnat := 
            (S (S (S (S (S O))))).



Check (S (S (S O))).
Check five.



Definition mnat_id_fun (n: mnat): mnat := n.



Compute mnat_id_fun (S (S (S O))).


Definition pred (n: mnat): mnat :=
  match n with
    | O => O 
    | S n' => n'
  end.



Example predOisO: pred O = O.

Proof. auto. Qed.



Example pred2is1: pred (S (S O)) = (S O).
Proof.
auto.
Qed.



Theorem pred_Sn : forall n:mnat, n = pred (S n).
Proof.
intros.
simpl.
reflexivity.
Qed.


Theorem CeroNoSuc: forall n:mnat, S n <> O.
Proof.
intros.
discriminate.
Qed.


Theorem SucIny : forall n m:mnat, S n = S m -> n = m.
Proof.
intros.
cut (n = pred (S n) ).
intros.
rewrite H0.
assert ( m = pred (S m) ).
apply pred_Sn.
rewrite H1.
rewrite H.
reflexivity.
apply pred_Sn.
Qed.



Fixpoint plus (n1 n2: mnat): mnat := 
  match n1 with
    | O => n2
    | (S n') => S (plus n' n2)
  end.



Theorem t1: forall n: mnat, (plus O n) = n.
Proof. auto. Qed.



Theorem t2: forall n: mnat, (plus n O) = n.
Proof.

auto.

induction n as [ | n'].



auto.



simpl.


rewrite IHn'.



auto.



Restart.

induction n as [ | n'].
auto.
compute.
unfold plus in IHn'.
rewrite IHn'.
reflexivity.



Restart.

induction n as [ | n'].

auto.

cbv delta.

cbv iota.

cbv beta.

cbv iota.

cbv beta.

unfold plus in IHn'.
rewrite IHn'.
reflexivity.

Qed.


Lemma suma_Sn_m: forall n m:mnat, plus n (S m)  = S (plus n m).
Proof.
admit.
Qed.

Theorem Conm_suma: forall n m: mnat, plus n m = plus m n.
Proof.
intros.
induction n.
simpl.
rewrite t2.
reflexivity.
simpl.
rewrite IHn.
rewrite suma_Sn_m.
reflexivity.
Qed.


Fixpoint mult (n m:mnat): mnat :=
  match n with
  | O => O
  | S p => plus m (mult p m)
  end.




End MiNat.

Search nat.

Require Import Lt.

Search le.


Require Import List.

Print list.

Search In.
