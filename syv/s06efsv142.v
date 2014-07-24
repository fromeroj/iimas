(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 6, Logica intuicionista y clásica *)


Section NegIntuicionista.

Variables p q r s t:Prop.

Theorem ExFalso: False -> p.
Proof.
intros.
elim H. 
Qed.


Theorem texcimp: (p \/ ~p) -> ~~p -> p.
Proof.
unfold not.
intros.
elim H.
intuition.
intros.
exfalso.
apply H0.
trivial.
Qed.

Theorem defimp: (~p \/ q) -> p -> q.
Proof.
unfold not.
intros.
destruct H.
exfalso.
intuition.
trivial.
Qed.


Theorem Absurdo: p /\ ~p -> q.
Proof.
intros.
destruct H.
unfold not in H0.
elim H0.
trivial.
Qed.

Check Absurdo.

Check absurd.


Theorem SilogismoDisy: (p \/ q) /\ ~p -> q.
Proof.
intro.
destruct H.
destruct H.
absurd p.
trivial.
trivial.
trivial.
Qed.






Theorem SyssNeg: (p <-> q) <-> (~p <-> ~ q).
Proof.
unfold iff.
split.
intros.
destruct H.
split.
intros.
unfold not.
intros.
apply H1.
apply H0; assumption.
intros.
intro.
apply H1;apply H;assumption.
intros.
destruct H.
split.
intro.
exfalso.
apply H.
apply H0.
apply H.
apply H0.
Admitted.


End NegIntuicionista.



Require Import Classical.

Parameters (p q r s u v C:Prop)
           (A: Set)
           (a:A)
           (P: A -> Prop)
           (R: A -> A -> Prop).




Check classic.

Check classic u.

Check classic (u\/v).

Check NNPP.

Check NNPP v.

Check NNPP (u -> v).

Theorem edn: ~~p <-> p.
Proof.
unfold iff.
split.
exact (NNPP p).
intros.
unfold not.
intros.
exact (H0 H).
Qed.

Print edn.
Print NNPP.
Print classic.



Theorem ContraPos: (p -> q) <-> (~q -> ~p).
Proof.
unfold iff.
split.
intuition.
intros.
assert (q \/ ~q).
exact (classic q).
destruct H1.
exact H1.
absurd p.
exact (H H1).
exact H0.
Qed.

Print ContraPos.

Search or.

Theorem DefImp: (p -> q) <-> ~p \/ q.
Proof.
unfold iff.
split.
intro.
assert (p\/~p).
exact (classic p).
destruct H0.
right;exact(H H0).
left;assumption.
intros.
destruct H.
absurd p;trivial;trivial.
trivial.
Qed.

Theorem TEDebil: ((p -> q) -> q) \/ (p->q).
Proof. 
assert ((p->q)\/ ~(p ->q)).
exact (classic(p->q)).
destruct H as [I|N].
right;trivial.
left;intro.
absurd (p -> q);trivial;trivial.
Qed.

Lemma dMorganY: forall p q:Prop, ~(p/\q) <-> ~p \/ ~q.
Proof. Admitted.

Lemma dMorganO: forall p q:Prop, ~(p\/q) <-> ~p /\ ~q.
Proof. Admitted.


Check dMorganY.
Check dMorganO.

Lemma dMorganOi: forall p q:Prop, ~(p\/q) -> ~p /\ ~q.
Proof.
intros p q.
assert (~ (p \/ q) <-> ~ p /\ ~ q).
exact (dMorganO p q).
destruct H.
exact H.
Qed.







Lemma NegImpC: ~(p->q) -> p /\ ~ q.
Proof.
intros.
cut (~~p/\~q).
intros.
destruct H0.
split.
exact ((NNPP p) H0).
trivial.
cut(~(~p \/ q)).
exact (dMorganOi (~p) q ).

contradict H.
intros.
destruct H.
absurd p; assumption; assumption.

assumption.
Qed.


Theorem GoedelDummet: (p -> q) \/ (q -> p).
Proof.
cut ((p -> q) \/ ~(p->q)).
intro.
destruct H as [I|N]. 
left;trivial.
cut (p /\ ~ q).
intro.
destruct H as [P NQ].
right.
intro.
absurd q;trivial;trivial.

(* Versión cut*)
cut (~ (p -> q) -> p /\ ~ q).
intros.
exact (H N).
exact NegImpC.
exact (classic (p-> q)).

(* Versión assert *)
(*
assert (~ (p -> q) -> p /\ ~ q).
exact NegImpC.
exact (H N).
exact (classic (p-> q)).
*)
Qed.

Check GoedelDummet.


Theorem PrenexO:  (C \/ forall x:A, P x ) <-> forall x:A, C \/ P x.
Proof.
unfold iff.
split.
intro D.
destruct D as [D1|D2].
intro x0.
left.
trivial.
intro y0.
right.
apply D2.
intro H.
cut (C \/ ~ C).
intro T.
destruct T as [T1|T2].
left;trivial.
right.
intro z0.
destruct H with z0.
exfalso.
exact (T2 H0).
exact H0.
exact (classic C).
Qed.

Theorem DMorganGb:  (~ forall x:A, P x) -> (exists x:A, ~ P x).
Proof.
intro H.
cut (~~ exists x:A,~P x).
exact (NNPP (exists x:A,~P x)).
intro N.
apply H.
intro z.
cut (~~ P z).
exact (NNPP (P z)).
intro.
apply N.
exists z.
exact H0.
Qed.


(*
Theorem DMorganGb:  (~ forall x:A, P x) -> (exists x:A, ~ P x).
Proof.
intro H.
cut (~~ exists x:A,~P x).
exact (NNPP (exists x:A,~P x)).
intro N.
apply H.
intro z.
cut (~~ P z).
exact (NNPP (P z)).
intro.
apply N.
exists z.
exact H0.
Qed.
*)


Theorem Bebedor: exists x:A, P x -> forall y:A, P y.
Proof.
assert ((forall y:A, P y) \/ ~(forall y:A, P y)).
exact (classic (forall y:A, P y)).
destruct H as [H1|H2].
exists a.
intro.
exact H1.
cut (exists z:A, ~ P z).
intro E.
destruct E.
exists x.
intro.
exfalso.
exact (H H0).
cut (~ forall z:A,P z).
exact (DMorganGb).
exact H2.
Qed.


Theorem Barbero:  ~ exists x, forall y, R x y <-> ~ R y y.
Proof.
intro E.
destruct E.
destruct H with x.
assert (R x x \/ ~ R x x).
exact (classic (R x x)).
destruct H2 as [R1|R2].
apply H0.
trivial.
trivial.
apply H0.
exact (H1 R2).
exact (H1 R2).
Qed.


