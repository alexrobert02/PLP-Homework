(* 1. *)

Inductive Tree (T : Type) : Type :=
  | Empty : Tree T
  | Leaf : T -> Tree T
  | Branch : T -> Tree T -> Tree T -> Tree T.

Arguments Empty {T}.
Arguments Leaf {T}.
Arguments Branch {T}.

Definition t :=
  Branch 1 (Empty) (Branch 2 (Leaf 7)(Leaf 9)).

Print t.


(* 2. *)

Fixpoint mirror {T : Type} (t : Tree T) :=
  match t with
  | Empty => Empty
  | Leaf T => Leaf T
  | Branch T t1 t2 => Branch T (mirror t2) (mirror t1)
end.

Compute mirror (t).


(* 3. *)

Theorem convultive :
  forall {T : Type} (t : Tree T), (mirror (mirror t)) = t.
Proof.
  induction t0.
  reflexivity.
  simpl.
  trivial.
  simpl.
  rewrite IHt0_1.
  rewrite IHt0_2.
  trivial.
Qed.


(* 4. *)

Fixpoint process {T : Type} (f : T -> T) (t : Tree T) : (Tree T) :=
  match t with  
  | Empty => Empty
  | Leaf x => Leaf (f x)
  | Branch x t1 t2 => Branch (f x) (process f t1) (process f t2) 
end.

Definition incrementTree := process (fun x => x + 1) t.
Compute incrementTree.

Definition doubleTree := process (fun x => x * 2) t.
Compute doubleTree.

Definition squareTree := process (fun x => x * x) t.
Compute squareTree.


(* 5. *)

Theorem and_elim_1:
  forall (A B : Prop), A /\ B -> A.
Proof.
  intros.
  apply H.
Qed.

Theorem and_elim_2:
  forall (A B : Prop), A /\ B -> B.
Proof.
  intros.
  apply H.
Qed.

Theorem and_intro:
  forall (A B : Prop), A -> B -> (A /\ B).
Proof.
  intros.
  split.
  - apply H.
  - apply H0.
Qed.

Theorem or_elim:
  forall (A B C: Prop), (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros.
  destruct H1.
  - apply H. apply H1.
  - apply H0. apply H1.
Qed.

Theorem or_intro_1:
  forall (A B : Prop), A -> (A \/ B).
Proof.
  intros.
  left.
  apply H.
Qed.

Theorem or_intro_2:
  forall (A B : Prop), B -> (A \/ B).
Proof.
  intros.
  right.
  apply H.
Qed.

Theorem not_not:
  forall (P : Prop), P -> ~~P.
Proof.
  intros.
  unfold not.
  intros HP.
  apply HP.
  apply H.
Qed.

Theorem mp :
  forall A B,
    (A -> B) -> A -> B.
Proof.
  intros.
  apply X.
  apply X0.
Qed.

Theorem mt :
  forall (A B : Prop),
    (A -> B) -> ~ B -> ~ A.
Proof.
  intros.
  unfold not in H0.
  unfold not.
  auto.
Qed.