Require Import String.


Inductive Exp :=
| anum : nat -> Exp
| avar : string -> Exp
| aplus : Exp -> Exp -> Exp
| amult : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| blessthan : Exp -> Exp -> Exp.
                          

Coercion anum : nat >-> Exp.
Coercion avar : string >-> Exp.
Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A *' B" := (amult A B) (at level 40, left associativity).
Notation "A <' B" := (blessthan A B) (at level 60).
Notation "A &&' B" := (band A B) (at level 750, left associativity).


Check 2 +' 2.
Check 2 +' btrue.
Check 2 +' (4 <' 3).



Definition Env := string -> nat.
Definition update
           (sigma : Env)
           (x : string)
           (v : nat) : Env :=
  fun y => if eqb x y
           then v
           else (sigma y).


Reserved Notation "A -[ S ]-> B"
         (at level 90).


Inductive eval :
  Exp -> Env -> Exp -> Prop :=
| const : forall i sigma,
    (anum i) -[ sigma ]-> i
| lookup : forall x sigma,
    (avar x) -[ sigma ]-> (sigma x)
| add_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 +' a2) -[ sigma ]-> (a1' +' a2)
| add_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 +' a2) -[ sigma ]-> (a1 +' a2')
| add : forall i1 i2 sigma n,
    n = i1 + i2 -> 
    (i1 +' i2) -[ sigma ]-> n
| mul_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 *' a2) -[ sigma ]-> (a1' *' a2)
| mul_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 *' a2) -[ sigma ]-> (a1 *' a2')
| mul : forall i1 i2 sigma n,
    n = i1 * i2 -> 
    (i1 *' i2) -[ sigma ]-> n
| etrue : forall sigma,
  btrue -[ sigma ]-> btrue
| efalse : forall sigma,
  bfalse -[ sigma ]-> bfalse
| lessthan_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 <' a2) -[ sigma ]-> (a1' <' a2)
| lessthan_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 <' a2) -[ sigma ]-> (a1 <' a2')
| lessthan_ : forall i1 i2 sigma b,
    b = (if Nat.ltb i1 i2 then btrue else bfalse) -> 
    (i1 <' i2) -[ sigma ]-> b
| not_1: forall b b' sigma,
    b -[ sigma ]-> b' ->
    (bnot b) -[ sigma ]-> (bnot b')
| not_t : forall sigma,
    (bnot btrue) -[ sigma ]-> bfalse
| not_f : forall sigma,
    (bnot bfalse) -[ sigma ]-> btrue
| band_1 : forall b1 b2 b1' sigma,
    b1 -[ sigma ]-> b1' ->
    (band b1 b2) -[ sigma ]-> (band b1' b2)
| band_true : forall b2 sigma,
    (band btrue b2) -[ sigma ]-> b2
| band_false : forall b2 sigma,
  (band bfalse b2) -[ sigma ]-> b2
where "A -[ S ]-> B" := (eval A S B).

Reserved Notation "A -[ S ]>* B"
         (at level 90).
Inductive eval_closure :
  Exp -> Env -> Exp -> Prop :=
| refl : forall e sigma,
    e -[ sigma ]>* e
| tran : forall e1 e2 e3 sigma,
  e1 -[ sigma ]-> e2 ->
  e2 -[ sigma ]>* e3 ->
  e1 -[ sigma ]>* e3      
where "A -[ S ]>* B" :=
  (eval_closure A S B).

Create HintDb types.
#[local] Hint Constructors Exp : types.
#[local] Hint Constructors eval : types.
#[local] Hint Constructors eval_closure : types.

Definition Env0 : Env := fun x => 0.

#[local] Hint Unfold Env0 : types.
#[local] Hint Unfold update : types.


Open Scope string_scope.
Example e1:
  2 +' "n" -[ Env0 ]>* 2.
Proof.
  eapply tran.
  - eapply add_r.
    apply lookup.
  - unfold Env0, update.
    eapply tran.
    + apply add. simpl. reflexivity.
    + apply refl.
Qed.


Example e1':
  2 +' "n" -[ Env0 ]>* 2.
Proof.
  eauto with types.
Qed.

Example e2:
  "n" +' "n" -[ Env0 ]>* 0.
Proof.
  eauto 10 with types.
Qed.


Example e2':
  "n" +' "n" -[ Env0 ]>* btrue.
Proof.
  eauto 10  with types.
Abort.



(* TYPES *)
Inductive Typ :=
| Nat
| Bool.

Print Exp.

Inductive type_of : Exp -> Typ -> Prop :=
| t_num: forall n,
    type_of (anum n) Nat
| t_var: forall x,
    type_of (avar x) Nat
| t_plus: forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat ->
    type_of (a1 +' a2) Nat
| t_mult: forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat ->
    type_of (a1 *' a2) Nat
| t_true: type_of btrue Bool
| t_false: type_of bfalse Bool
| t_not: forall b,
    type_of b Bool -> 
    type_of (bnot b) Bool
| t_and: forall b1 b2,
    type_of b1 Bool ->
    type_of b2 Bool -> 
    type_of (band b1 b2) Bool
| t_lessthan: forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat -> 
    type_of (blessthan a1 a2) Bool.

#[local] Hint Constructors Typ : types.
#[local] Hint Constructors type_of : types.

Example t1:
  type_of  (2 +' "n") Nat.
Proof.
  apply t_plus.
  - apply t_num.
  - apply t_var.
Qed.
  
Example t2:
  type_of  (2 +' btrue) Nat.
Proof.
  apply t_plus.
  - apply t_num.
  - (* can't prove that *)
Abort.


(* values *)
Inductive nat_value : Exp -> Prop :=
| n_val : forall n, nat_value (anum n).

Inductive bool_value : Exp -> Prop :=
| b_true : bool_value btrue
| b_false : bool_value bfalse.

Definition value (e : Exp) : Prop :=
  nat_value e \/ bool_value e.


#[local] Hint Constructors nat_value : types.
#[local] Hint Constructors bool_value : types.
#[local] Hint Unfold value : types.


Lemma bool_canonical:
  forall e, 
    type_of e Bool ->
    value e ->
    bool_value e.        
Proof.
  intros e H H'.
  inversion H'; eauto with types.
  inversion H; eauto with types; subst;
    inversion H0.
Qed.


Lemma nat_canonical:
  forall e, 
    type_of e Nat ->
    value e ->
    nat_value e.        
Proof.
  intros e H H'.
  inversion H'; eauto with types.
  inversion H; eauto with types; subst;
    inversion H0.
Qed.

    

Theorem progress:
  forall e T sigma,
  type_of e T ->
  (value e \/ exists e', e -[ sigma ]-> e').
Proof.
  intros e T sigma H.
  induction H; eauto with types.
  - destruct IHtype_of1 as [H1 | [e1 H1]];
      eauto with types.
    destruct IHtype_of2 as [H2 | [e2 H2]];
      eauto with types.
    apply nat_canonical in H; auto.
    apply nat_canonical in H0; auto.
    right.
    inversion H; eauto with types. 
  - destruct IHtype_of1 as [H1 | [e1 H1]];
      eauto with types.
    destruct IHtype_of2 as [H2 | [e2 H2]];
      eauto with types.
    apply nat_canonical in H; auto.
    apply nat_canonical in H0; auto.
    right.
    inversion H. inversion H0.
    eexists.
    apply mul. reflexivity.
  - destruct IHtype_of as [H1 | [e1 H1]];
      eauto with types.
    apply bool_canonical in H; auto.
    inversion H; subst; right; eauto with types.
  - destruct IHtype_of1 as [H1 | [e1 H1]];
      eauto with types.
    destruct IHtype_of2 as [H2 | [e2 H2]];
      eauto with types.
    apply bool_canonical in H; auto.
    inversion H; eauto with types.
    apply bool_canonical in H; auto.
    right.
    eexists.
    inversion H; eauto with types.
  - destruct IHtype_of1 as [H1 | [e1 H1]];
      eauto with types.
    destruct IHtype_of2 as [H2 | [e2 H2]];
      eauto with types.
    apply nat_canonical in H; auto.
    apply nat_canonical in H0; auto.
    right.
    inversion H. inversion H0.
    eexists; eauto with types.
Qed.


Theorem preservation:
  forall e e' T sigma,
    type_of e T ->
    e -[ sigma ]-> e' ->
    type_of e' T.
Proof.
  intros e e' T sigma H H'.
  revert e' H'.
  induction H; intros e' H';
    inversion H'; subst; eauto with types.
  case_eq (Nat.ltb i1 i2); intros; eauto with types.
Qed.

  
Theorem soundness:
  forall e e' T sigma,
    type_of e T ->
    e -[ sigma ]>* e' ->
    (value e' \/
       exists e'', e' -[ sigma ]-> e'').
Proof.
  intros e e' T sigma H H'.
  induction H'.
  - eapply progress. eauto.
  - eapply preservation in H0; eauto.
Qed.