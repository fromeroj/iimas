(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 4, Logica minimal proposicional*)


Section LogMinimal.

Variables p q r s t:Prop.


(* Lemas para las reglas de introduccion y eliminacion *)

Lemma MP: (p -> q) -> p -> q.
Proof.
intros. 
apply H.
trivial.
Qed.

Lemma ImpI: (p -> q) -> (p -> q).
Proof.
intros.
apply H.
trivial.
Qed.

Lemma ConjI: p -> q -> p /\ q.
Proof.
intros.
split.
trivial.
trivial.
Qed.


Lemma ConjE: p /\ q -> p.
Proof.
intros.
elim H.
intros.
trivial.
Qed.


Lemma DisyI: p -> p \/ q.
Proof.
intro.
left.
trivial.
Qed.


Lemma DisyE: (p -> r) -> (q -> r) -> p \/ q -> r.
Proof.
intros.
elim H1.
trivial.
trivial.
Qed.

(* Ejemplos con implicacion *)

Theorem Imptrans : (p -> q) -> (q -> s) -> (p -> s).
Proof.
intro h1.
intro h2.
intro h3.
apply h2.
apply h1.
exact h3.
Qed.

Check Imptrans.


Theorem Imptrans2 : (p -> q) -> (q -> s) -> (p -> s).
Proof.
intro.
intro.
intro.
apply H0. 
apply H.
exact H1.
Qed.

Check Imptrans2.


Theorem Imptrans3 : (p -> q) -> (q -> s) -> (p -> s).
Proof.
intros.
apply H0.
apply H.
exact H1.
Qed.

Check Imptrans3. 


Theorem Imptrans4 : (p -> q) -> (q -> s) -> (p -> s).
Proof.
auto.
Qed.

Check Imptrans4.



(* Ejemplos con conjuncion *)

Theorem ImpExp: p /\ q -> r -> p -> q -> r.
Proof.
auto.
Qed.


Theorem ImpExp2: (p /\ q -> r) -> p -> q -> r.
Proof.
intros.
apply H.
split.
assumption.
assumption.
Qed.

Check ImpExp2.

Print ImpExp2.


Theorem ImpExp3: (p /\ q -> r) -> p -> q -> r.
Proof.
intros.
apply H.
split.
exact H0.
exact H1.
Qed.


Theorem ImpExp4: p /\ q -> r -> p -> q -> r.
Proof.
intros.
destruct H.
trivial.
Qed.


Theorem ExpImp: (p -> q -> r) -> p /\ q -> r.
Proof.
intros.
apply H.
elim H0.
intros.
exact H1.
elim H0.
intros.
exact H2.
Qed.


Print ExpImp.


Theorem ExpImp2: (p -> q -> r) -> p /\ q -> r.
Proof.
intros.
destruct H0.
apply H.
trivial.

trivial.
Qed.


Theorem DistrImpl: (p -> q -> r) -> (p -> q) -> (p -> r).
Proof.
intros H1 H2 H3.
apply H1.
assumption.
exact (H2 H3).
Qed.




(* Ejemplos con disyuncion *)


Theorem Disy2: q \/ p -> p \/ q.
Proof.
intros.
elim H.
intros.
right.
assumption.
intros.
left.
exact H0.
Qed.

Print Disy2.


Theorem DilemaC : (p -> q) -> (r -> s) -> p \/ r -> q \/ s. 
Proof.
intros.
elim H1.
intro.
left.
apply H.
assumption.
intro.
right.
apply H0.
exact H2.
Qed.

Print DilemaC.

Theorem DilemaC2 : (p -> q) -> (r -> s) -> p \/ r -> q \/ s. 
Proof.
intros.
destruct H1.
left.
apply H. 
trivial.
right.
exact (H0 H1).
Qed.



Theorem DisyAsoc: p \/ (q \/ r) ->  (p \/ q) \/ r.

Proof.
intros.
destruct H.
left;left.
trivial.
destruct H.
left;right;trivial.
right;trivial.
Qed.


Theorem Absorcion1: p \/ (p /\ q) -> p.
Proof.
intros.
destruct H.
trivial.
destruct H.
trivial.
Qed.


Theorem Absorcion2: p -> p \/ (p /\ q).
Proof.
auto.
Qed.


(* Ejemplos más elaborados *)


Theorem Absorcion: p <-> p \/ (p /\ q).
Proof.
unfold iff.
split.
intros.
left.
trivial.
intros.
destruct H.
trivial.
destruct H.
trivial.
Qed.



Theorem Distrib : p \/ (q /\ r) -> (p \/ q) /\ (p \/ r).
Proof.
intros.
split.
elim H.
intro.
left.
assumption.
intro.
right.
elim H0.
intros.
assumption.
elim H.
intros.
left.
assumption.
intros.
elim H0.
intros.
right.
assumption.
Qed.

Print Distrib.

Theorem Distrib2 : p /\ (q \/ r) -> (p /\ q) \/ (p /\ r).
Proof.
intros.
destruct H.
destruct H0.
left.
split.
trivial.
trivial.
right.
split.
trivial.
trivial.
Qed.


Theorem DisyImp: p \/ q -> (p -> q) -> q.
Proof.
intros.
destruct H as [H1|H2].
apply H0.
trivial.
trivial.
Qed.




Theorem SyssImp : (p <-> q) -> ((p -> r) <-> (q -> r)).
Proof.
intros.
unfold iff in H.
unfold iff.
split.
intros.
destruct H.
exact (H0 (H2 H1)).
intros.
destruct H.
apply H0.
apply H.
trivial.
Qed.




Theorem SyssImp2 : (p <-> q) -> ((p -> r) <-> (q -> r)).
Proof.
intros.
unfold iff.
split.
intros.
apply H0.
destruct H.
apply H2.
apply H.
apply H2.
trivial.
intros.
apply H0.
destruct H.
apply H.
apply H2.
apply H.
trivial.
Qed.


Lemma SyssP: (p <-> q) -> p -> q.
Proof.
intros E P.
destruct E as [E1 E2].
exact (E1 P).
Qed.

Lemma SyssQ: (p <-> q) -> q -> p.
Proof.
intros E Q.
destruct E as [E1 E2].
exact (E2 Q).
Qed.


Theorem SyssImp2L : (p <-> q) -> ((p -> r) <-> (q -> r)).
Proof.
intros.
unfold iff.
split.
intros.
apply H0.
exact (SyssQ H H1).
intros H1 H2.
apply H1.
exact (SyssP H H2).
Qed.



Hypotheses b z c d:Prop.

Theorem Argumento1: (b /\ z) /\ (z -> c /\ d) /\ (c /\ b -> q) -> q \/t.
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
left.
apply H3.
split.
destruct H1 as [H4 H5].
apply H2.
trivial.
destruct H1.
trivial.
Qed.


Check SyssP.

End LogMinimal.


Check SyssP.


Section CutAssert.

Hypotheses (p q r t : Prop)
           (H: p -> q) 

           (H1: q -> r)
           (H2: (p -> r) -> t -> q)
           (H3: (p -> r) -> t).

Theorem cu: q.
Proof.
apply H2.
intro.
apply H1.
apply H.
exact H0.
apply H3.
intro.
apply H1.
apply H.
exact H0.
Qed.

Lemma SilHip: (p -> q) -> (q -> r) -> (p -> r).
Proof.
auto.
Qed.


Theorem cu2: q.
Proof.
apply H2.
exact (SilHip H H1).
apply H3.
exact (SilHip H H1).
Qed.


Theorem cu3: q.
Proof.
cut (p -> r).
intro.
apply H2.
assumption. 
apply H3. 
assumption.
exact (SilHip H H1).
Qed.


End CutAssert.



Section NegMinimal.

Variables p q r s t:Prop.


Theorem negacion: p -> ~~p.
Proof.
intros.
unfold not.
intros.
apply H0.
assumption.
Qed.

Theorem nonoTExc: ~~(p \/ ~p).
Proof.
unfold not.
intros.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.





Theorem NegImp: (p -> q) -> (p -> ~q) -> ~p.
Proof.
intros.
unfold not.
intro.
assert q.
apply H.
assumption.
assert (~q).
apply H0.
assumption.
unfold not in H3.
apply H3.
assumption.
Qed.

Theorem NegImpConj: p /\ ~q -> ~(p -> q).
Proof.
intro.
unfold not.
intro.
destruct H.
assert q.
apply H0.
trivial.
apply H1.  (* Obsérvese que no hay necesidad de desdoblar la definición de ~*)
trivial.
Qed.





Theorem dmorganO : ~ ( p \/ q ) <-> ~p /\ ~q.
Proof.
unfold iff.
split.
unfold not.
intro.
split.
intro.
apply H.
left.
assumption.

intros.
apply H.
right.
assumption.

unfold not.
intros.
elim H.
intros.
elim H0.
exact H1.
exact H2.
Qed.


Theorem defimp: (~p \/ q) -> p -> q.
Proof.
unfold not.
intros.
elim H.
intros.
elim H1.
assumption.
intro;assumption.
Qed.


Theorem defimp2: (~p \/ q) -> p -> q.
Proof.
intros.
unfold not in H.
destruct H.
elim H.
trivial.
trivial.
Qed.


Theorem Contrapositiva: (p -> q) -> (~q -> ~p).
Proof.
intros.
unfold not in H0.
unfold not.
intro.
apply H0.
apply H.
trivial.
Qed.


Theorem ContrapositivaNegDebil: (p -> ~q) <-> (q -> ~p).
Proof.
unfold iff.
split.
intros.
intro.
apply H.
assumption.
assumption.
intros.
intro.
apply H.
exact H1. 
exact H0.
Qed. 

End NegMinimal.
