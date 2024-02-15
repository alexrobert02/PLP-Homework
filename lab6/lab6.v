Require Import String.
Open Scope string_scope.


(* 1. *)

(* mapping string |-> nat *)
Definition Env := string -> nat.
Definition update
           (env : string -> nat)
           (x   : string)
           (v   : nat) :
  (string -> nat) :=

  fun y => if eqb y x
           then v
           else (env y).

Inductive Exp :=
| var : string -> Exp
| num : nat -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion var : string >-> Exp.
Coercion num : nat >-> Exp.

Notation "A +' B" := (add A B)
                      (at level 50,
                        left associativity).

Notation "A -' B" := (sub A B)
                       (left associativity,
                         at level 50).

Notation "A /' B" := (div A B)
                      (at level 40,
                        left associativity).

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive ExpEval : Exp -> Env -> nat -> Prop :=
| Num : forall i sigma, num i =[sigma]=> i
| Var : forall x sigma, var x =[sigma]=> sigma x
| Add: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma]=> i1 ->
  a2 =[sigma]=> i2 ->
  n  = i1 + i2 ->
  a1 +' a2 =[sigma]=> n
| Sub: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma]=> i1 ->
  a2 =[sigma]=> i2 ->
  n  = Nat.sub i1 i2 ->
  a1 -' a2 =[sigma]=> n
| Div: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma]=> i1 ->
  a2 =[sigma]=> i2 ->
  n  = Nat.div i1 i2 ->
  a1 /' a2 =[sigma]=> n
where "A =[ S ]=> N" := (ExpEval A S N).

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| band : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.

Notation "! A" := (bnot A) (at level 70).
Notation "A =' B" := (beq A B) (at level 60).
Notation "A <' B" := (less A B) (at level 60).
Notation "A &' B" := (band A B) (at level 80).

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90).

Definition Env1 := update (fun x => 0) "n" 10.
Compute Env1 "n".

Example ExpEval1:
  2 +' "n" =[ Env1 ]=> 2 + 10.
Proof.
  (* v1:
  apply Add with (i1 := 2) (i2 := 10).
   *)
  eapply Add.
  - apply Num.
  - apply Var.
  - reflexivity.
Qed.

Example ExpEval2:
  15 -' "n" =[ Env1 ]=> 15 - 10.
Proof.
  eapply Sub with (i1 := 15) (i2 := 10).
  - apply Num.
  - apply Var.
  - simpl. trivial.
Qed.

Example ExpEval3:
  20 /' "n" =[ Env1 ]=> Nat.div 20 10.
Proof.
  eapply Div.
  - apply Num.
  - apply Var.
  - auto.
Qed.

Inductive CondEval : Cond -> Env -> bool -> Prop :=
| T : forall sigma b, b ={ sigma }=> true
| F : forall sigma b, b ={ sigma }=> false
| NotT : forall b sigma,
    b ={ sigma }=> true ->
    bnot b ={ sigma }=> false 
| NotF : forall b sigma,
    b ={ sigma }=> false ->
    bnot b ={ sigma }=> true
| EqT : forall a1 a2 i1 i2 b sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b = Nat.eqb i1 i2 ->
  a1 =' a2 ={ sigma }=> b
| EqF : forall a1 a2 i1 i2 b sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b = negb (Nat.eqb i1 i2) ->
  a1 =' a2 ={ sigma }=> false
| Lt : forall a1 a2 i1 i2 b sigma, 
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b  = Nat.ltb i1 i2 ->
  a1 <' a2 ={ sigma }=> b 
| AndT : forall b1 b2 sigma b,
   b1 ={ sigma }=> true ->
   b2 ={ sigma }=> b ->
   b1 &' b2 ={ sigma }=> b
| AndF : forall b1 b2 sigma,
   b1 ={ sigma }=> false ->
   b1 &' b2 ={ sigma }=> false
where "B ={ Sigma }=> B'" := (CondEval B Sigma B').

#[local] Hint Constructors CondEval : mydb.

(*eauto with mydb.*)

Example CondEval1:
  2 +' 8 =' "n" ={ Env1 }=> true.
Proof.
  eapply EqT.
  - eapply Add. eapply Num. eapply Num. simpl. trivial.
  - eapply Var.
  - trivial.
Qed.

Example CondEval2:
  2 +' "n" <' 13 ={ Env1 }=> true.
Proof.
  eapply Lt with (i2 := 13).
   - eapply ExpEval1.
   - apply Num.
   - reflexivity.
Qed.

Example CondEval3:
  4 +' 13 =' 17 &' 15 -' "n" <' 5 ={ Env1 }=> false.
Proof.
  eapply AndT.
    - eapply EqT.
      + eapply Add. eapply Num. eapply Num. trivial.
      + eapply Num.
      + reflexivity.
    - eapply Lt.
      + eapply Sub. eapply Num. eapply Var. auto.
      + eapply Num.
      + auto.
Qed.


(* 2. *)

Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "X ::= V" := (assign X V) (at level 85).
Notation "S1 ;; S2" := (seq S1 S2) (right associativity, at level 99).

Reserved Notation "S1 -[ Sigma ]-> Sigma'" (at level 99).

Inductive StmtEval : Stmt -> Env -> Env -> Prop :=
| Skip : forall sigma,
  skip -[ sigma ]-> sigma
| Assign: forall a i sigma x sigma',
  a =[ sigma ]=> i ->
  sigma' = update sigma x i ->
  (x ::= a) -[ sigma ]-> sigma'
| Seq : forall s1 s2 sigma sigma0 sigma',
  s1 -[ sigma ]-> sigma0 ->
  s2 -[ sigma0 ]-> sigma' ->
  (s1 ;; s2) -[ sigma ]-> sigma'
| IteT : forall s1 s2 sigma sigma1 b,
  b ={ sigma }=> true ->
  s1 -[ sigma ]-> sigma1 ->
  (ite b s1 s2) -[ sigma ]-> sigma1
| IteF : forall s1 s2 sigma sigma2 b,
  b ={ sigma }=> false ->
  s2 -[ sigma ]-> sigma2 ->
  (ite b s1 s2) -[ sigma ]-> sigma2
| IfT : forall sigma sigma' b s,
  b ={ sigma }=> true ->
  s -[ sigma ]-> sigma' ->
  (it b s) -[ sigma ]-> sigma'
| IfF : forall sigma b s,
  b ={ sigma }=> false ->
  (it b s) -[ sigma ]-> sigma
| DoWhileF : forall b sigma s sigma',
  b ={ sigma }=> false ->
  (dowhile s b) -[ sigma ]-> sigma'
| DoWhileT : forall b sigma s sigma',
  b ={ sigma }=> true ->
  (s ;; dowhile s b) -[ sigma ]-> sigma' ->
  (dowhile s b) -[ sigma ]-> sigma'
where "S1 -[ Sigma ]-> Sigma'" := (StmtEval S1 Sigma Sigma').

#[local] Hint Constructors StmtEval : mydb.

Example StmtEval1:
  exists Env2,
    ("n" ::= 100 -[ Env1 ]-> Env2) /\
      (Env2 = update Env1 "n" 100).
Proof.
  eexists.
  split.
  - eapply Assign.
    + apply Num.
    + reflexivity.
  - reflexivity.
Qed.

Example StmtEval2:
  ("n" ::= 0 ;;
  dowhile ("n" ::= "n" +' 1) ("n" <'1)) -[ Env1 ]-> update (update Env1 "n" 0) "n" 1.
Proof.
  eapply Seq.
  - eapply Assign.
    + eapply Num.
    + eauto.
  - eapply DoWhileT.
    + eapply Lt.
      ++ eapply Var.
      ++ eapply Num.
      ++ eauto.
    + eapply Seq.
      ++ eapply Assign.
        +++ eapply Add. eapply Var. eapply Num. eauto.
        +++ eauto.
      ++ eapply DoWhileF.
        +++ eapply Lt.
          ++++ eapply Var.
          ++++ eapply Num.
          ++++ eauto.
Qed.

Example StmtEval3:
  ("n" ::= 4 ;;
  it ("n" <' 5) ("n" ::= "n" +' 3)) -[ Env1 ]-> (update (update Env1 "n" 4) "n" 7).
Proof.
  eapply Seq.
  - eapply Assign.
    + eapply Num.
    + eauto.
  - eapply IfT.
    + eapply Lt.
      ++ eapply Var.
      ++ eapply Num.
      ++ trivial.
    + eapply Assign.
      ++ eapply Add.
        +++ eapply Var. 
        +++ eapply Num.
        +++ eauto.
      ++ eauto.
Qed.

Example StmtEval14:
  ("n" ::= 8 ;;
  it ("n" =' 5) ("n" ::= "n" +' 4)) -[ Env1 ]-> (update Env1 "n" 8).
Proof.
  eapply Seq.
  - eapply Assign.
    + eapply Num.
    + eauto.
  - eapply IfF.
    + eapply EqF.
      ++ eapply Var.
      ++ eapply Num.
      ++ eauto.
Qed.

Example StmtEval15:
  ("n" ::= 3 ;;
  ite ("n" =' 3) ("n" ::= "n" +' 2) ("n" ::= "n" +' 1)) -[ Env1 ]-> (update (update Env1 "n" 3) "n" 5).
Proof.
  eapply Seq.
  - eapply Assign.
    + eapply Num.
    + eauto.
  - eapply IteT.
    + eapply EqT.
      ++ eapply Var.
      ++ eapply Num.
      ++ eauto.
    + eapply Assign.
      ++ eapply Add.
        +++ eapply Var. 
        +++ eapply Num.
        +++ eauto.
      ++ eauto.
Qed.

Example StmtEval16:
  ("n" ::= 3 ;;
  ite ("n" <' 3) ("n" ::= "n" +' 5) ("n" ::= "n" +' 9)) -[ Env1 ]-> (update (update Env1 "n" 3) "n" 12).
Proof.
  eapply Seq.
  - eapply Assign.
    + eapply Num.
    + eauto.
  - eapply IteF.
    + eapply Lt.
      ++ eapply Var.
      ++ eapply Num.
      ++ eauto.
    + eapply Assign.
      ++ eapply Add.
        +++ eapply Var. 
        +++ eapply Num.
        +++ eauto.
      ++ eauto.
Qed.
