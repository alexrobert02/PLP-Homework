Require Import Coq.Arith.Plus.
Open Scope nat_scope.


Inductive Nat :=
| O : Nat
| S : Nat -> Nat.

Fixpoint le_Nat (m n : Nat) : bool :=
  match m with
  | O    => true
  | S m' => match n with
            | O    => false
            | S n' => le_Nat m' n'
            end
  end.

Compute le_Nat O O.
Compute le_Nat (S O) O.
Compute le_Nat O (S O).


Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
(*  intros. *)
  induction m.
  - simpl. reflexivity.
  - intros.
    simpl in H.
    destruct n as [|n'].
    -- inversion H.
    -- simpl in H0.
       destruct p.
       --- inversion H0.
       --- simpl.
           apply IHm with (n := n');
           assumption.
Qed.


Inductive List (T : Type) : Type :=
| Nil : List T
| Cons : T -> List T -> List T.

Check List.

Definition ListNat := List nat.
Definition ListBool := List bool.

Check Nil.
Check Cons.

Arguments Nil {T}.
Arguments Cons {T}.

Fixpoint length (T : Type) (l : List T) : nat := 
  match l with
  | Nil => 0
  | Cons _ l' => 1 + (length T l')
  end.


Definition l1 := (Cons 2 Nil).
Definition l2 := (Cons 5 l1).

Arguments length {T}.

Definition l1' := Cons 2 Nil. (* [2] *)
Definition l2' := Cons 5 l1'. (* [5;2] *) 

Compute length l1'.
Compute length l2'.

Fixpoint filter {T : Type}
         (f : T -> bool)
         (l : List T) :=
  match l with
  | Nil => Nil
  | Cons x xs => if (f x)
                 then Cons x (filter f xs)
                 else filter f xs
  end.

Definition is_digit (n : nat) : bool :=
  Nat.leb n 9.

Check is_digit.

Compute filter is_digit l2'.
Compute filter is_digit
        (Cons 12 (Cons 4 (Cons 15 Nil))).

Compute filter (fun n => Nat.leb n 12)
        (Cons 12 (Cons 4 (Cons 15 Nil))).

Check (fun n => Nat.leb n 12).
Check Nat.leb.


(* <= : nat -> nat -> bool  (* curried a tipului de mai jos *) *)
(* <= : nat x nat -> bool                       *)

Check Nat.leb.
(* Check (Nat.leb _ 5). *)

Definition id {T : Type} (f : T) := f.

Check id Nat.leb.
Check id is_digit.

Definition compose {A : Type} {B : Type} {C : Type}
           (f : A -> B)
           (g : B -> C) : A -> C :=
  fun x => g (f x).

Compute compose
        (fun n => 2 * n)
        (fun n => 3 + n)
        10.

Compute compose
        (fun n => 3 + n)
        (fun n => 2 * n)
        10.



Check (fun (b : bool) => if b then Nil else (Cons 1 Nil)).

Check (fun n => Nat.leb n 9).

Compute compose
        (fun n => Nat.leb n 9)
        (fun (b:bool) => if b then Nil else (Cons 1 Nil))
        1.

Check compose.

(* Proofs *)


Check 10 = 10.
Check 10 = 11.

Check True.
Check False.

Check true.
Check false.

Print bool.


Lemma test1 :
  forall (n m : nat),
    n = m.
Admitted.

    
Lemma test2:
  forall (n m : nat),
    n = 0 ->
    m = 0 ->
    n + m = 0.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  trivial.
Qed.

Lemma mp :
  forall p q,
    p ->
    (p -> q) ->
    q.
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Lemma conj:
  2 + 2 = 4 /\ 5 + 3 = 8.
Proof.
  split; trivial.
Qed.

Lemma conj2:
  forall n m,
    (n = 0 /\ m = 0) ->
    n + m = 0.
Proof.
  (* intros n m [H1 H2]. *)
  intros.
  destruct H as [H1 H2].
Admitted.


Lemma disj:
  2 + 2 = 5 \/ 2 + 3 = 5.
Proof.
  right.
  simpl.
  trivial.
Qed.

  
Lemma exist2:
  exists (n : nat), n = 0.
Proof.
  exists 0.
  trivial.
Qed.


Lemma exist_3:
  forall m,
    (exists n, m = n + 2) ->
    (exists n', m = n' + 1).
Proof.
  intros.
  destruct H as [n0 Hn0].
  exists (n0 + 1).
  rewrite <- plus_assoc.
  simpl.
  trivial.
Qed.


Goal
  (forall n, n > 0) ->
  4 > 0.
Proof.
  intros.
  apply H.
Qed.

Lemma add_assoc_local:
  forall a b c,
    a + (b + c) = (a + b) + c.
Proof.
  induction a; trivial.
  intros.
  simpl.
  rewrite IHa.
  trivial.
Qed.


Lemma application:
  forall a b c d,
    (a + b) + (c + d) =
      a + (b + (c + d)).
Proof.
  intros.
  rewrite add_assoc_local.

  rewrite add_assoc_local.
  rewrite add_assoc_local.
  trivial.
Qed.