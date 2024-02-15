Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.


Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
  end.

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.


Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.


Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.


(* 1. *)

Fixpoint le_Nat (m n : Nat) : bool :=
  match m with
  | O => true
  | S m' => match n with
            | O => false
            | S n' => le_Nat m' n'
            end
  end.

Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)


(* 2. *)

Lemma le_then_O :
  forall n,
    le_Nat n O = true ->
    n = O.
Proof.
    induction n.    
    - simpl. trivial.
    - simpl. intros. inversion H.
Qed.


(* 3. *)

Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
    induction x.
    - trivial.
    - simpl. rewrite IHx. trivial.
Qed.

Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
  induction m.
  - trivial.
  - intros.
    rewrite <- H0.
    inversion H.
    destruct n as [|n'].
    -- inversion H2.
    -- destruct p.
       --- auto.
       --- simpl.
           inversion H0.
           rewrite H3.
           apply IHm with (n := n').
           assumption.
           trivial.
Qed.


(* 4. *)

Lemma le_add :
  forall x y,
    le_Nat x (add x y) = true.
Proof.
  induction x.
  - simpl. trivial.
  - intros.
    simpl.
    destruct x as [|x'].
    + simpl. trivial.
    + trivial.
Qed.


(* 5. *)

Lemma le_add_consistent :
  forall m n k,
    le_Nat m n = true ->
    le_Nat m (add n k) = true.
Proof.
    induction m.
    - simpl. trivial.
    - intros.
      simpl in H.
      destruct n as [|n'].
      inversion H.
      simpl.
      auto.
Qed. 


(* 6. *)

Lemma le_max_true :
  forall m n,
    le_Nat m n = true ->
    max m n = n.
Proof.
    induction m.
    - simpl. trivial.
    - intros.
      simpl in H.
      destruct n as [|n'].
      + inversion H.
      + simpl. rewrite IHm.
        trivial.
        trivial.
Qed.


(* 7. *)

Lemma le_max_false :
  forall m n,
    le_Nat m n = false ->
    max m n = m.
Proof.
  induction m.
  - simpl.
    intros.
    inversion H.
  - intros.
    simpl in H.
    destruct n as [|n'].
    + trivial.
    + simpl. rewrite IHm.
      trivial.
      trivial.
Qed.
