Require Import ArithRing.

Inductive binario: Type :=
  | cero : binario
  | consb : bool -> binario -> binario.

Notation "x :: l" := (consb x l) (at level 60, right associativity).
Notation "[ ]" := cero.
Notation "[ x , .. , y ]" := (consb x .. (consb y cero) ..).

(*
 Funciones de N->N que necesito
    doble      usando sucesores.
    mas_uno    que el sucesor es lo mismo que sumar uno
    doble como suma  que doble de n es n +n
*)
Fixpoint doble (n:nat) : nat :=
  match n with
    | O => O
    | S n' => S (S (doble n'))
  end.

Lemma repr: [false]=[].
Admitted.

Lemma mas_uno: forall (n:nat), S n = n + 1.
Proof.
  intros.
  compute.
  induction n.
  reflexivity.
  rewrite IHn.
  reflexivity.
  Qed.

Lemma doble_como_suma: forall (n:nat), doble(n) = n + n.
Proof.
  induction n.
  compute.
  reflexivity.
  assert( K: S n + S n = S ( S (n + n))).
  ring.
  rewrite K.
  simpl.
  rewrite IHn.
  ring.
  Qed.

(*
   Operaciones básicas con binarios
   binc   incrementar el numero binario.
   b2n    transformar un binario a natural
   n2b    transformar un natural a binario
   suma_binaria  
   producto_binario
*)

(* binc   incrementar el numero binario. *)
Fixpoint binc (b:binario) : binario :=
  match b with
    | cero => [ true ]
    | false::xs => true::xs
    | true::xs  => false::(binc xs)
  end.

(* b2n    transformar un binario a natural *)
Fixpoint b2n (b:binario) : nat :=
  match b with
    | cero => 0
    | false::bs => doble (b2n bs)
    | true::bs  => S (doble (b2n bs))
  end.

(* n2b    transformar un natural a binario *)
Fixpoint n2b (n:nat) : binario :=
  match n with
    | 0 => cero
    | S n' => binc (n2b n')
  end.

Fixpoint suma_binaria (x:binario) (y:binario): binario :=
  match x,y with
    | cero,y => y
    | x,cero => x
    | (false::xs),(true::ys) => true::(suma_binaria xs ys)
    | (false::xs),(false::ys) => false::(suma_binaria xs ys)
    | (true::xs),(false::ys) => true::(suma_binaria xs ys)
    | (true::xs),(true::ys) => false::(binc(suma_binaria xs ys))
    end.

Fixpoint producto_binario (x:binario) (y:binario): binario :=
  match x,y with
    | cero,y => cero
    | (false::xs),y => false::(producto_binario xs y) 
    | (true::xs),y => suma_binaria y (false::(producto_binario xs y)) 
    end.

Fixpoint representacion (b:binario) : binario :=
  match b with
    | false::bs => bs
    | _  => b
  end.

(* Ejemplitos, por pura diversion *)
Compute binc([true,true,false,true]).
Eval simpl in (n2b (b2n [])).
Eval simpl in (b2n [true,true,true]).
Eval simpl in (b2n [false,true,true]).
Eval simpl in (n2b 7).
Eval simpl in (n2b 6).
Eval simpl in (n2b (b2n [false,true,true])).
Eval simpl in b2n (suma_binaria (n2b 17) (n2b 2)).
Eval simpl in b2n (producto_binario (n2b 17) (n2b 2)).

(* Lemas utiles para cuando vengan los casos de suma y producto *)

(* sbinc; incrementar el binario y convertirlo a natural
          es lo mismo que convertirlo primero y tomar al sucesor*)
Lemma sbinc: forall (b:binario), b2n (binc b) = S (b2n b).
Proof.
  intros.
  induction b.
  simpl.
  reflexivity.
  destruct b.
  simpl.
  rewrite IHb.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  Qed.


(* En la suma binaria, sumar 0 de cualquier lado da el otro sumando *)
Lemma zsuma_der: forall (x:binario), suma_binaria x cero = x.
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    destruct b;simpl;reflexivity.
    Qed.
Lemma zsuma_izq: forall (x:binario), suma_binaria cero x = x.
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    destruct b;simpl;reflexivity.
    Qed.

(* transformar un natural a binario y de regreso regresa el numero inicial *)
Theorem n2b2n_id : forall n:nat, b2n (n2b n) = n.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite sbinc.
  rewrite IHn.
  reflexivity.
Qed.

Lemma suma_x_sy: forall (x y:binario), suma_binaria (binc x) y = binc (suma_binaria x y).
Admitted.

Theorem suma_es_correcta: forall (x:nat), forall (y:nat), 
                x+y = b2n(suma_binaria (n2b x) (n2b y)).
Proof.
  intros.
  induction x.
  simpl.
  rewrite n2b2n_id.
  reflexivity.
  simpl.
  rewrite mas_uno.
  rewrite suma_x_sy.
  rewrite sbinc.
  rewrite IHx.
  assert(K: S (b2n (suma_binaria (n2b x) (n2b y))) =b2n (suma_binaria (n2b x) (n2b y)) +1 ).
 rewrite mas_uno.
 reflexivity.
  rewrite <- K.
   reflexivity.
Qed.


Lemma producto_zero_izq: forall (x:binario), producto_binario [] x=cero.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.


(*
USA REPR
*)
Lemma producto_zero_der: forall (x:binario), producto_binario x []=cero.
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite IHx.
    apply repr.
    simpl.
    rewrite IHx.
    apply repr.
  Qed.

Lemma producto_uno: forall (x:binario), producto_binario x [true]=x.
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite IHx.
    reflexivity.
    simpl.
    rewrite IHx.
    reflexivity.
    Qed.

Lemma fact_xx: forall(x y: binario), producto_binario (false::x) y = producto_binario x (false:: y).
  Proof.
    intros.
    simpl.
    induction x.
    simpl.
    rewrite repr.
    reflexivity.
    destruct b.
    simpl.
    rewrite IHx.
    reflexivity.
    simpl.
    rewrite IHx.
    reflexivity.
    Qed.

Lemma fact_yy: forall(x y: binario), producto_binario (true::x) y = suma_binaria y (producto_binario (false::x) y).
  Proof.
    intros.
    simpl.
    reflexivity.
    Qed.

Lemma fact_xx2: forall(x y: binario), producto_binario (false::x) y = false::(producto_binario x y).
  Proof.
    intros.
    induction y.
    simpl.
    rewrite producto_zero_der.
    reflexivity.
    simpl.
    reflexivity.
    Qed.
  
Lemma fact_xx3: forall(x y: binario), producto_binario x (false::y) = false::(producto_binario x y).
  Proof.
    intros.
    induction y.
    rewrite repr.
    rewrite producto_zero_der.
    rewrite repr.
    reflexivity.
    destruct b.
    



Lemma fact_yy2: forall(x y: binario), producto_binario x (true::y) = suma_binaria x (producto_binario x (false::y)).
  Proof.
    intros.
    induction y.
    simpl.
    rewrite repr.
    rewrite producto_zero_der.
    rewrite zsuma_der.
    rewrite producto_uno.
    reflexivity.
    destruct b.
    

    simpl.

    Qed.


Lemma prod_conmuta: forall(x y: binario), producto_binario x y=producto_binario y x.
  Proof.
    intros.
    induction x.
    simpl.
    rewrite producto_zero_der.
    reflexivity.
    destruct b.
    simpl.
    
    rewrite fact_xx.

    rewrite <- fact_yy.
    

    

    induction y.
    rewrite producto_zero_izq.
    rewrite producto_zero_der.
    reflexivity.
    induction x.
    simpl.
    destruct b.
    rewrite producto_zero_der.
    rewrite repr.
    reflexivity.
    rewrite producto_zero_der.
    rewrite repr.
    reflexivity.
    destruct b.
    destruct b0.

    compute.


    simpl.
    


Lemma doble_pr: forall(x y: binario), false::(producto_binario x y)= producto_binario x (false::y).
Proof.
  intros.



  induction y.
  rewrite producto_zero_der.
  rewrite repr.
  rewrite producto_zero_der.
  reflexivity.
  destruct b.
  induction x.
  simpl.
  rewrite repr.
  reflexivity.
  

  rewrite repr.
  assert (K: suma_binaria x [] = x).
  rewrite zsuma_der.
  reflexivity.
  rewrite K.
  reflexivity.
Qed.
  
Lemma doble_pr2: forall (x y :binario), false::(producto_binario x y)=producto_binario x (false::y).
  Proof.
    intros.
    induction y.
    rewrite producto_zero_der.
    rewrite repr.
    rewrite producto_zero_der.
    reflexivity.
    destruct b.
    





Theorem producto_distribuye: forall (x y z:binario), producto_binario (suma_binaria x  y) z =suma_binaria (producto_binario  x z) (producto_binario y z).
  Proof.
    intros.
    induction z.
    simpl.
    rewrite producto_zero_der.
    simpl.
    rewrite producto_zero_der.
    rewrite producto_zero_der.
    simpl.
    reflexivity.
    destruct b.
    
    
    


    compute.



Theorem producto_es_correcto: forall (x:nat), forall (y:nat), x*y =b2n(producto_binario (n2b x) (n2b y)).
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    rewrite mas_uno.
    assert (H: (x+1)*y = x * y +y ).
    ring.
    rewrite H.
    rewrite IHx.
    


(*


Theorem df: forall b:binario, suma_binaria b [true] = binc b.
  Proof.
    intros.
    induction b.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite <- IHb.
    assert(K: binc (suma_binaria b0 []) =  suma_binaria b0 [true]).
    rewrite IHb.
    rewrite zsuma_der.
    reflexivity.
    rewrite K.
    reflexivity.
    simpl.
    rewrite zsuma_der.
    simpl.
    reflexivity.
    Qed.

Lemma suma_x_sy: forall (x y:binario), suma_binaria (binc x) y = binc (suma_binaria x y).
Admitted.

Proof.
  intros.
  rewrite <-df.
  

  destruct x.
  rewrite zsuma_izq.
  induction y.
  simpl.
  reflexivity.
  destruct b.
  rewrite <- df.
  rewrite zsuma_izq.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  induction y.
  rewrite zsuma_izq.
  rewrite zsuma_izq.
  reflexivity.
  rewrite <- df.
  rewrite <- df.
  destruct b.
  rewrite df.
  rewrite df.

  simpl.


  rewrite doble_binario_1.
  
  simpl.
  
  admit.
  

  induction x.
  induction y.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  destruct b.
  admit.
  rewrite doble_binario.
*)  

(*
Lemma bincz: forall (x:binario), binc (false::x)=true::x.
  Proof.
    intros.
    simpl.
    reflexivity.
    Qed.

Lemma binczf: forall (x:binario), binc (true::x)=false::binc(x).
  Proof.
    intros.
    simpl.
    reflexivity.
    Qed.
*)

(*
Lemma suma_sx_y: forall (x y:binario), suma_binaria x (binc y) = binc (suma_binaria x y).
Admitted.
*)

(*  Proof.
    intros.
    rewrite inc_as_sum.
    rewrite inc_as_sum.
    induction x.
    rewrite zsuma_izq.
    rewrite zsuma_izq.
    induction y.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite zsuma_izq.
    reflexivity.
    simpl.
    rewrite zsuma_izq.
    reflexivity.
    destruct b.
    induction y.
    rewrite zsuma_izq.
    rewrite zsuma_izq.
    reflexivity.
    destruct b.
    simpl.
    rewrite zsuma_izq.
    rewrite zsuma_izq.
    rewrite inc_as_sum.
    rewrite inc_as_sum.
    induction x.
    rewrite zsuma_izq.
    rewrite inc_as_sum2.
    rewrite inc_as_sum2.
    assert( J: suma_binaria [true] [] = [true]).
    simpl.
    reflexivity.
    rewrite J.
    reflexivity.
    destruct b.
    rewrite inc_as_sum.
    rewrite inc_as_sum.
    induction y.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite zsuma_izq.
    rewrite zsuma_izq.
    rewrite inc_as_sum.
    rewrite inc_as_sum.
    

    rewrite binczf.
    
    
    

    Qed.
*)
(*
Lemma suma_doble:forall (y:binario), suma_binaria y y = false::y.
  Proof.
    intros.
    induction y.
    simpl.
    admit.
    destruct b.
    simpl.
    rewrite IHy.
    simpl.
    reflexivity.
    simpl.
    rewrite IHy.
    simpl.
    reflexivity.
    Qed.


Lemma paso: forall (x y: binario), suma_binaria (true::x) y = binc ( suma_binaria x (suma_binaria x y)).
  Admitted.
    
Lemma suma_doble_i: forall (y:binario), 
           (true :: y) = (binc (suma_binaria y y)).
  Proof.
    intros.
    induction y.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite IHy.
    reflexivity.
    simpl.
    rewrite suma_doble.
    reflexivity.
    Qed.

Theorem df: forall b:binario, (b2n b) + 1 = b2n (binc b). 
  Proof.
    intros.
    induction b.
    simpl.
    reflexivity.
    destruct b.
    simpl.
    rewrite <- IHb.
    simpl.
    rewrite doble_como_suma.
    rewrite doble_como_suma.
    










Lemma reflex: forall (x:binario), forall (y:binario), suma_binaria x y=suma_binaria y x.
  Proof.
    Admitted.
(*
    intros.
    induction x.
    simpl.
    rewrite zsuma.
    reflexivity.
    destruct b.
    rewrite suma_doble_i.
    admit.
    rewrite <- suma_doble.
*)

Lemma trans: forall (x :binario) (y z:binario), suma_binaria x (suma_binaria y z) = suma_binaria (suma_binaria x y) z. 
  Proof.
    intro.
    induction x.
    simpl.
    reflexivity.
    destruct b.
    intros.
    rewrite paso.
    rewrite paso.
    rewrite suma_x_sy.
    rewrite IHx.
    admit.
    rewrite <- suma_doble.
    
    
    
    
    

    induction y.
    simpl.
    rewrite zsuma.
    induction z.
    rewrite zsuma.
    rewrite zsuma.
    reflexivity.
    destruct b.

    

    rewrite zsuma in IHx.
    rewrite zsuma2 in IHx.



    rewrite IHx.


    rewrite zsuma.
    rewrite zsuma.
    reflexivity.
    destruct b.
    rewrite suma_doble_i.
    rewrite suma_sx_y.
    rewrite suma_sx_y.
    rewrite suma_sx_y.
    



    

    induction y.
    simpl.
    rewrite zsuma.
    reflexivity.
    induction x.
    rewrite zsuma2.
    rewrite zsuma2.
    reflexivity.
    rewrite suma_doble.
    destruct b0.
    rewrite suma_doble_i.
    rewrite suma_doble.
    rewrite bincz.
    rewrite bincz.
    destruct b.
    simpl.
  

(*

  *)  
    
    
Lemma a1: forall (x:binario), forall (y:binario), 
           b2n (suma_binaria x (false :: y)) =b2n( suma_binaria (suma_binaria x y) y).
  Admitted.





  
  

  
  assert (k:     )




  rewrite J.


  induction x.
  simpl.

  




  induction y.

  simpl.
  reflexivity.
  rewrite J.
  assert( K: b2n (b :: x) + 0  = b2n (b :: x)).
  ring.
  rewrite K.
  assert( H: suma_binaria (b :: x) [] = b :: x ).
  compute.

  rewrite H.
  reflexivity.
  destruct b.
  assert (I:  b2n (true :: x) = 1 + b2n x  + b2n x).
  simpl.
  assert (I2: doble (b2n x) = b2n x  + b2n x).
  apply doble_como_suma.
  rewrite I2.
  reflexivity.
  rewrite I.
  
  

  induction x.
  simpl.
  reflexivity.
  

  


Eval simpl in (suma_binaria [false,true,true,true] [true,true,true]).



(*

*)


(*

*)





Definition imp_id_proof := fun (p:Prop) => (fun (d:p) => d).

Check imp_id_proof (3=3).
Check imp_id_proof (3=3) (refl_equal 3).

Theorem imp_id : forall I:Prop, I -> I.
  intro p.
  intro d.
  exact d.
Qed.

Print imp_id.

(*
Eval simpl in binc (normalize (O (I (O Cero)))) = (normalize (I (I (O Cero)))).
*)

Definition binariodoble (b:binario) : binario :=
  match b with
    | Cero => Cero
    | O n' => O (O n')
    | I n' => O (I n')
  end.

Lemma binc_twice : forall b:binario,
  binc (binc (binariodoble b)) = binariodoble (binc b).
  Proof.
    destruct b.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.

Lemma doble_binariodoble : forall n:nat,
  n2b (doble n) = (binariodoble (n2b n)).
  Proof.
    intro n.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn.
    rewrite binc_twice.
    reflexivity.
  Qed.

Lemma binc_binariodoble: forall b:binario,
  binc (binariodoble b) = I b.
  intro b.
  destruct b.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem b2n2binario_n_eq_norm_n : forall b:binario,
  n2b (b2n b) = normalize b.
  Proof.
    intro b.
    induction b.
    reflexivity.
    simpl.
    rewrite doble_binariodoble.
    rewrite IHb.
    unfold binariodoble.
    reflexivity.
    simpl.
    rewrite doble_binariodoble.
    rewrite IHb.
    rewrite binc_binariodoble.
    reflexivity.
  Qed.

(*
Lemma doble_como_suma_b: forall (x:binario), doble (b2n x) = b2n x  + b2n x.
  Proof.
    intros.
    rewrite doble_como_suma.
    reflexivity.
  Qed.


Lemma inc_as_sum: forall (x :binario), binc x= suma_binaria x [true].
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    destruct b;simpl;rewrite zsuma;reflexivity.
    Qed.

Lemma inc_as_sum2: forall (x :binario), binc x= suma_binaria [true] x.
  Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    destruct b;simpl;reflexivity.
    Qed.
*)