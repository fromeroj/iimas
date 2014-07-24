(* Especificación Formal MCIC - Semántica y Verificación LCC
   Dr. Favio Miranda
   Script 1, Números y booleanos. *)


Require Import Arith.

(* Ejemplos *) 

(* Función a,b |-> b + 2(a+b)  *)

Definition foo (a b : nat) := b + 2 * (a + b).

(* Función que suma las componentes de un par de naturales, uso de pattern matching *)

Definition suma_par (p : nat * nat) :=
  match p with 
   (a, b) => a + b end.

(* EJERCICIO 1: definir la función "suma_cuadrados" que devuelve la suma de los cuadrados de dos números. 
                  Usar el comando Compute para calcular suma_cuadrados(5,3) *)

Definition suma_cuadrados a b := a*a + b*b.

Check suma_cuadrados.

Compute suma_cuadrados 5 3.



(* EJERCICIO 3: definir la función "suma5" que toma 5 números y devuelve su suma. 
                 Calcula suma5(1,2,3,4,5) *)

Definition suma5 a b c d e := a+b+c+d+e.

Compute suma5 1 2 3 4 5.

(* EJERCICIO 4: definir la función "incrementa5" que suma 5 a un número dado. Calcula incrementa5(4)  *)

Definition incrementa5 a := a+5.

Compute incrementa5 4.

(* EJERCICIO 5: Definir la función composición en nat->nat. *)

Definition comp (f g:nat -> nat) x := f (g x).


(* Funciones con pares *)

(* Ejercicio 6: definir la función "psu" función que recibe un par de numeros (a,b) y regresa 
            el par (a + 1, b) *)

Definition psu (p:nat*nat) := match p with (a,b) => (a+1,b) end.

(* Ejercicio 7: definir la función "npar" que recibe un par de numeros (a,b) y 
       regresa un par donde el primer componenete es a+1 y el segundo es el producto
        de (a+1) por b.) *)



(* Ejercicio 8: definir la funcion "afpar" que recibe una función f de tipo (nat -> nat -> nat) 
          y un par de números (a,b)  y regresa el par (a+1, f a b) *)




(* Si la definición es correcta el resultado del siguiente test deber ser (3,13) *)




(* Si la definición es correcta el resultado del siguiente test deber ser (3,13) *)




(*Ejercicio 9: definir la función "agfpar" que recibe tres argumentos, el primero es 
    una función g de tipo (nat -> nat), una función f de tipo (nat -> nat -> nat) y un par de 
    naturales (a,b). El resultado debe ser el par (g a, f a b) *)

Definition agfpar (g:nat -> nat) (f:nat -> nat -> nat) p := match p with (a,b) => (g a,f a b) end.


(* Si la definición es correcta el resultado del siguiente test debe ser (7,29) *)

Compute agfpar incrementa5 suma_cuadrados (2,5). 



(* El comando "Search" busca funciones definidas en un tipo *)
Search nat.
Search bool.

(* El comando "Print" muestra la defininición de una funcion *)
Print foo.

Print suma5. 

(* EJERCICIO 10:  Observar la definición y el comportamiento de las funciones Div2.double, Div2.div2, y leb ,
   usando "Compute" *)


Compute Div2.double 13.

Print Div2.double.

Compute Div2.div2 13.

Compute Div2.div2 16.

Print Div2.div2.

Compute leb 6.

Check leb.

Print leb.

(* Usar estas 3 funciones únicamente para definir una función even : nat -> bool
   que decida si un número es par *)




(* EJERCICIO 11: definir la función "iter2p" que recibe dos argumentos, el primer argumento una función f 
          de tipo na*nat -> nat*nat  y un par de números p. Y devuelve el resultado de iterar dos veces 
           la función f, es decir, iter2p f p = f (f p) *)



(* Si la definición es correcta el siguiente test devuelve
  (1, 2, (2, 3))   *)

(*
Compute
   (iter2p (fun p => (snd p, fst p)) (1, 2),
    iter2p (fun p => (fst p + 1, snd p + fst p + 1)) (0,0)).
*)


(* Ejercicio 12: la función "leb" puede ser utilizada para comparar dos
         naturales. Usa esta función para definir la función "sm" que 
         recibe dos naturales a y b y devuelve a + 1 si a>=b y b en otro caso.
         Utiliza el constructor if ... then ... else ...*) 




(* Si la definición es correcta el resultado del siguiente test es 5. 
Compute sm 4 4.
*)

(* Si la definición es correcta el resultado del siguiente test debe ser 6. 
Compute sm 4 6.
*)


(*  TAREA 1 *)

(* La siguiente definición describe el cálculo del par
   (8, 8!), donde 8! = 1 * 2 * ... * 7 * 8 *)

Definition computo1 :=
  (fun f h p => f (f (f h)) p)
    (fun g p => g (g p))
    (fun p => match p with (x, y) => (x+1, (x+1) * y) end)
    (0, 1).

Compute computo1.


(* A.- Alguna parte de computo1 puede reemplazarse por  iter2p, 
  realiza el cambio y llama a la nueva función como computo2 

Compute computo2.

*)

(* B.- computo1 se puede modificar de tal forma que calcule (8, 1 + 2 + .. + 8), 
   realiza el cambio y nombrala computo3. *)



(* Si tu definición es correcta el siguiente test debe regresar (8, 36) 
Compute computo3.
*)

(* C.-  f aparece tres veces en  (f (f (f h))) y  g dos veces en (g (g p)),
   ¿cuál es la relación con el número 8?
   Modificar la función computo1 para que calcule (32, 1 + 2 + .. + 32) y 
   nombrar la nueva función como computo4 *)



(*  Si la definición es correcta el resultado del siguiente test debe ser (32, 528)) 
Compute computo4.
*)




Inductive bool : Set :=
  | true : bool
  | false : bool.



Definition good: bool := true.

Definition bad := false.



Definition bool_true (b: bool): bool := true.
Definition bool_false (b: bool): bool := false.
Definition bool_id (b: bool): bool := b.

Definition notb (b: bool): bool := 
  match b with 
    | true => false
    | false => true
  end.


Definition bool_binop := bool -> bool -> bool.


Definition andb (b1 b2: bool): bool := 
  match b1 with
    | true => b2
    | _ => false
  end.



Definition orb (b1 b2: bool): bool := 
  match b1 with
    | true => true
    | _ => b2
  end.




Theorem false_id_orb: forall b: bool, 
                        (orb b false) = b.
Proof.
induction b.
compute; reflexivity.
compute; reflexivity.
Qed.






Theorem and_commut: forall x y: bool,
                     (andb x y) = (andb y x).
Proof.
induction x.
induction y.
compute.
reflexivity.
compute; reflexivity.
induction y.
compute; reflexivity.
compute; reflexivity.
Qed.


Theorem or_assoc: forall x y z: bool,
  (orb z (orb y x)) = (orb (orb z y) x).
Proof.

induction x.
induction y.
induction z.
compute.
reflexivity.
compute;reflexivity.
induction z.
compute;reflexivity.
compute;reflexivity.
induction y.
induction z.
compute;reflexivity.
compute;reflexivity.
induction z.
compute;reflexivity.
compute;reflexivity.
Qed.


(*
http://coq.inria.fr/library/Coq.Init.Datatypes.html
*)


Module MiNat.


Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.



Definition zero: nat := O.

Print zero.


Definition one: nat := S O.


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


Definition five: nat := 
            (S (S (S (S (S O))))).



Check (S (S (S O))).
Check five.



Definition nat_id_fun (n: nat): nat := n.



Compute nat_id_fun (S (S (S O))).


Definition pred (n: nat): nat :=
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




Fixpoint plus (n1 n2: nat): nat := 
  match n1 with
    | O => n2
    | (S n') => S (plus n' n2)
  end.



Theorem t1: forall n: nat, (plus O n) = n.
Proof. auto. Qed.



Theorem t2: forall n: nat, (plus n O) = n.
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

End MiNat.
