(* EspecIficación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 3, listas de números naturales *)




(* Tipo inductivo de listas de naturales *)

Inductive listnat: Type :=
  | niln : listnat
  | consn : nat -> listnat -> listnat.


Notation "x :: l" := (consn x l) (at level 60, right associativity).

Notation "[ ]" := niln.

Notation "[ x , .. , y ]" := (consn x .. (consn y niln) ..).

Definition lista2 := 1 :: 2 :: 3 :: niln.

Print lista2.


(* Longitud *)

Fixpoint lg (l:listnat):nat :=
 match l with
  | niln => 0
  | consn h t => S (lg t)
 end.


(* Concatenacion *)




Fixpoint app (l1 l2:listnat):listnat :=
 match l1 with
  |niln => l2
  |h :: t => h :: (app t l2)
 end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).


Compute [1,2,3]++[6,7,8].

Fixpoint snoc n l :=
 match l with
  | niln => n :: niln
  | (h::t) => h :: snoc n t
 end.

Fixpoint rev l :=
 match l with
  | niln =>  niln
  | (h::t) => snoc h (rev t) 
 end.

Compute snoc 7 (1::2::8::niln).


(* Append con recursión en el primer argumento, usando snoc *)

Fixpoint appb l1 l2 :=
 match l2 with
  | niln => l1
  | h::t => appb (snoc h l1) t
 end.

Compute appb [1,2,3] [6,7,8].

Fixpoint zip l1 l2 :=
 match l1,l2 with
  | niln,l2 => nil
  | l1,niln => nil
  | h1::t1,h2::t2 => cons (h1,h2) (zip t1 t2)
 end.

Compute zip niln [13,88,100].

Compute zip [2,5,7,9] niln.

Compute zip [1,3,5,7] [2,4,6,8].


Fixpoint take (n:nat) (l:listnat) :=
 match n,l with
  | 0, l => niln
  | n, niln => niln
  | S n, consn h t => consn h (take n t)
 end.


Fixpoint repeatn (x n:nat) : listnat :=
 match n with
  | 0 => niln
  | S m => x :: (repeatn x m)
 end.

Fixpoint repeat (A:Set) (x:A) (n: nat) : list A :=
  match n with
  | O => nil
  | S m => cons x (repeat A x m)
  end.


Fixpoint takep (A:Type) (n:nat) (l:list A) :=
 match n,l with
  | 0, l => nil
  | n, nil => nil
  | S n, cons h t => cons h (takep A n t)
 end.


Fixpoint mapnat (f: nat -> nat) (l:listnat) :=
 match l with
  | niln => niln
  | h::t => f h :: mapnat f t
 end.

Compute mapnat (fun (x:nat) => x+1) [1,2,3,4].









(* Propiedades algebráicas de listas que probaremos más adelante *)

Theorem asocapp : forall l1 l2 l3:listnat, l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof. Admitted.

Theorem longapp : forall l1 l2:listnat, lg (l1 ++ l2) = lg l1 + lg l2.
Proof. Admitted.

Theorem snocdefapp : forall l:listnat, forall n:nat, snoc n l = app l [n].
Proof. Admitted. 

Theorem longrev : forall l:listnat, lg (rev l) = lg l.
Proof. Admitted.

Theorem idemprev : forall l:listnat, rev (rev l) = l.
Proof. Admitted.

Theorem revapp : forall l1 l2:listnat, rev(l1++l2) = rev l2 ++ rev l1.
Proof. Admitted.

Theorem snocapp : forall (l1 l2:listnat) (n:nat), snoc n (l1++l2) = app l1 (snoc n l2).
Proof. Admitted.

Theorem snocrev : forall (l:listnat) (n:nat), rev (snoc n l) = n :: rev l.
Proof. Admitted.

Theorem lgmapnat :  forall (f:nat -> nat) (l:listnat), lg (mapnat f l) = lg l.
Proof. Admitted.




(* Razonamiento sobre la función Inn *)

Fixpoint Inn (x:nat) (l: listnat)  :=
 match l with 
  | niln => False
  | (b::bs) => x = b \/ Inn x bs
 end.


Theorem inn_eq : forall (a:nat) (l:listnat), Inn a (a :: l).
Proof.
intros.
simpl.
left.
trivial.
Qed.


Theorem inn_nil : forall a:nat, ~ Inn a [].
Proof.
intros.
simpl.
unfold not.
intros.
trivial.
Qed.



Theorem inn_cons : forall (a b:nat) (l:listnat), Inn b l -> Inn b (a :: l).
Proof.
intros.
simpl.
right.
trivial.
Qed.


Theorem inn_split : forall (x:nat) (l:listnat), 
                      Inn x l -> exists l1, exists l2, l = l1 ++ (x::l2).

Proof.
intros.
induction l.
elim H.
destruct H.
exists niln.
simpl.
exists l.
rewrite H.
trivial.
assert (exists l1 : listnat, exists l2 : listnat, l = l1 ++ x :: l2).
apply IHl.
exact H.
destruct H0 as [l1'].
destruct H0 as [l2'].
exists (n::l1').
exists l2'.
simpl.
rewrite H0.
trivial.
Qed.


(*
simpl.
intros.
exists niln.
simpl.
exists l.
rewrite H0.
trivial.
intros.
*)


