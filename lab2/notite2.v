Inductive Nat :=
  O : Nat
| S : Nat -> Nat.

Check O.
Check (S O).
Check (S (S O)).
(* Error: Check S S. *)

Fixpoint plus (k m : Nat) : Nat :=
  match k with
  | O   => m
  | S n => S (plus n m)
  end.

Compute plus (S O) (S O).

(* Proof by simplification *)
Lemma plus_O_n_eq_n :
  forall n, plus O n = n.
Proof.
  (* tactics *)
  intro n.
  simpl.
  reflexivity.
Qed.

Print plus_O_n_eq_n.

(* Proof by rewriting *)
Lemma plus_eq :
  forall m n,
    m = n -> plus O m = plus O n.
Proof.
  intros m n H.
  rewrite <- H.
  reflexivity.
Qed.


(* Proof by case analysis *)
Lemma plus_c_a:
  forall k, plus k (S O) <> O.
Proof.
  intro k.
  destruct k as [|k']; simpl;
    unfold not; intro H;
    inversion H.
Qed.

Check Nat_ind.

Lemma plus_n_O_is_n:
  forall n, plus n O = n.
Proof.
  induction n.
  - simpl. trivial.
  - simpl. rewrite IHn. trivial.
Qed.


Theorem plus_comm:
  forall m n, plus m n = plus n m.
Proof.
  induction m.
  - intro n.
    simpl.
    rewrite plus_n_O_is_n.
    trivial.
  - induction n.
    + simpl. rewrite plus_n_O_is_n. trivial.
    + simpl.
      rewrite <- IHn.
      simpl.
      rewrite IHm.
      simpl.
      rewrite IHm.
      reflexivity.
Qed.