Require Import String.
Open Scope string_scope.


(* 1. *)

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

Reserved Notation "A =[ S ]=> N" (at level 70).

Inductive ExpEval :
  Exp -> Env -> Exp -> Prop :=
| Var : forall x sigma,
    var x =[ sigma ]=> (sigma x)
| Num : forall n sigma,
    num n =[ sigma ]=> n
| Add_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 +' a2 =[ sigma ]=> a1' +' a2
| Add_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    a1 +' a2 =[ sigma ]=> a1 +' a2'
| Add : forall i1 i2 sigma n,
        n = num (i1 + i2) ->
        i1 +' i2 =[ sigma ]=> n
| Sub_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 -' a2 =[ sigma ]=> a1' -' a2
| Sub_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    a1 -' a2 =[ sigma ]=> a1 -' a2'
| Sub : forall i1 i2 sigma n,
        n = num (Nat.sub i1 i2) ->
        i1 -' i2 =[ sigma ]=> n  
| Div_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 /' a2 =[ sigma ]=> a1' /' a2
| Div_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    a1 /' a2 =[ sigma ]=> a1 /' a2'
| Div : forall i1 i2 sigma n,
        n = num (Nat.div i1 i2) ->
        i1 /' i2 =[ sigma ]=> n   
where "A =[ S ]=> N" :=
  (ExpEval A S N).

Definition Env1 := update (fun x => 0) "n" 10.

Example ex1 : 2 +' "n" =[ Env1 ]=> 2 +' 10.
Proof.
  apply Add_2.
  apply Var.
Qed.

Example ex2 : "n" +' 2 =[ Env1 ]=> 10 +' 2.
Proof.
  apply Add_1.
  apply Var.
Qed.

Example ex3_oups : "n" +' 2 =[ Env1 ]=> 12.
Proof.
Abort.

Reserved Notation "A =[ S ]>* N" (at level 70).
Inductive ExpEvalClosure  :
  Exp -> Env -> Exp -> Prop :=
| a_refl : forall a sigma, a =[ sigma ]>* a
| a_tran : forall a1 a2 a3 sigma,
    (a1 =[ sigma ]=> a2) ->
    (a2 =[ sigma ]>* a3) ->
    (a1 =[ sigma ]>* a3)
where "A =[ S ]>* N" :=
  (ExpEvalClosure A S N).

Example ex3 : "n" +' 2 =[ Env1 ]>* 12.
Proof.
  eapply a_tran.
  - eapply Add_1.
    apply Var.
  - eapply a_tran.
    + unfold Env1. unfold update. simpl.
      apply Add. reflexivity.
    + simpl. apply a_refl.
Qed.

Create HintDb d1.
#[local] Hint Constructors ExpEval : d1.
#[local] Hint Constructors ExpEvalClosure : d1.

#[local] Hint Unfold Env1 : d1.
#[local] Hint Unfold update : d1.

Example ex3' : "n" +' 2 =[ Env1 ]>* 12.
Proof.
  eauto with d1.
Qed.

Print Env1.
Definition Env2 := update Env1 "m" 12.

Example ex4 : "n" +' "m" =[ Env2 ]>* 22.
Proof.
  eapply a_tran.
  - eapply Add_1.
    eapply Var.
  - eapply a_tran.
    + apply Add_2.
      eapply Var.
    + eapply a_tran.
      * unfold Env2, Env1. unfold update. simpl.
        apply Add.
        reflexivity.
      * simpl. apply a_refl.
Qed.

Example ex4' : "n" +' "m" =[ Env2 ]>* 22.
Proof.
  eapply a_tran.
  - eapply Add_2.
    eapply Var.
  - eapply a_tran.
    + apply Add_1.
      eapply Var.
    + eapply a_tran.
      * unfold Env2, Env1. unfold update. simpl.
        apply Add.
        reflexivity.
      * simpl. apply a_refl.
Qed.

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

Inductive CondEval :
  Cond -> Env -> Cond -> Prop :=
| Lt_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 <' a2 ={ sigma }=> a1' <' a2
| Lt_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (num i1) <' a2 ={ sigma }=> (num i1) <' a2'
| Lt : forall i1 i2 b sigma,
    b = (if Nat.ltb i1 i2 then true else false) ->
    (num i1) <' (num i2) ={ sigma }=> b
| Not : forall b b' sigma,
    b ={ sigma }=> b' ->
    (bnot b) ={ sigma }=> (bnot b')
| NotT : forall sigma,
    (bnot true) ={ sigma }=> false
| NotF : forall sigma,
    (bnot false) ={ sigma }=> true
| And_1 : forall b1 b1' sigma b2,
    b1 ={ sigma }=> b1' ->
    (band b1 b2) ={ sigma }=> (band b1' b2)
| AndF : forall b2 sigma,
    (band false b2) ={ sigma }=> false
| AndT : forall b2 sigma,
    (band true b2) ={ sigma }=> b2
where "B ={ S }=> B'" := (CondEval B S B').

Reserved Notation "B ={ S }>* B'" (at level 90).

Inductive CondEvalClosure : Cond -> Env -> Cond -> Prop :=
| b_refl : forall b sigma,
    b ={ sigma }>* b
| b_tran : forall b1 b2 b3 sigma,
    (b1 ={ sigma }=> b2) ->
    (b2 ={ sigma }>* b3) ->
    (b1 ={ sigma }>* b3)
where "B ={ S }>* B'" := (CondEvalClosure B S B').

Example ex5 : 1 +' 3 <' 5 ={ Env1 }>* true.
Proof.
  eapply b_tran.
  - eapply Lt_1.
    eapply Add.
    simpl. reflexivity.
  - eapply b_tran.
    + apply Lt.
      simpl. reflexivity.
    + apply b_refl.
Qed.

#[local] Hint Constructors CondEval:d1.
#[local] Hint Constructors CondEvalClosure:d1.


Example ex5' : 1 +' 3 <' 5 ={ Env1 }>* true.
Proof.
  eauto 10 with d1.
Qed.


(* 2. *)

Inductive Stmt :=
| skip : Stmt
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "S1 ;; S2" := (seq S1 S2)
                         (right associativity,
                           at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Reserved Notation "St1 -{ State }->[ St2 ; State' ]"
         (at level 100).

Inductive StmtEval :
  Stmt -> Env -> Stmt -> Env -> Prop :=
| Skip : forall s2 sigma,
    (skip ;; s2) -{ sigma }->[ s2 ; sigma ]
| Assing_2 : forall a a' x sigma,
    a =[ sigma ]=> a' -> 
    (x ::= a) -{ sigma }->[ x ::= a' ; sigma ]
| Assign : forall x i sigma,
    (x ::= (num i)) -{ sigma }->[ skip ; update sigma x i ]
| Seq : forall s1 s1' s2 sigma sigma',
    s1 -{ sigma }->[ s1' ; sigma' ] ->
    (s1 ;; s2) -{ sigma }->[ s1' ;; s2 ; sigma' ]
| Ite : forall b b' s s' sigma,
    b ={ sigma }=> b' ->
    ite b s s' -{ sigma }->[ ite b' s s' ; sigma ]
| IteT : forall s s' sigma,
    ite true s s' -{ sigma }->[ s ; sigma ]
| IteF : forall s s' sigma,
    ite false s s' -{ sigma }->[ s' ; sigma ]
| If : forall b b' s sigma,
    b ={ sigma }=> b' ->
    it b s -{ sigma }->[ it b' s ; sigma ]
| IfT : forall s s' sigma,
    it true s -{ sigma }->[ s' ; sigma ]
| IfF : forall s sigma,
    it false s -{ sigma }->[ s ; sigma ]
| DoWhile_ : forall b s sigma, 
     (dowhile s b) -{ sigma }->[ s ;; ite b (dowhile s b) skip  ; sigma ]
where "St1 -{ State }->[ St2 ; State' ]" := (StmtEval St1 State St2 State').

Reserved Notation "St1 -{ State }>*[ St2 ; State' ]"
         (at level 100).
Inductive StmtEvalClosure : Stmt -> Env -> Stmt -> Env -> Prop :=
| refl : forall s sigma, s -{ sigma }>*[ s ; sigma ]
| tran : forall s1 s2 s3 sigma1 sigma2 sigma3,
    s1 -{ sigma1 }->[ s2 ; sigma2 ] ->
    s2 -{ sigma2 }>*[ s3 ; sigma3 ] -> 
    s1 -{ sigma1 }>*[ s3 ; sigma3 ]
where "St1 -{ State }>*[ St2 ; State' ]" :=
  (StmtEvalClosure St1 State St2 State').

Example ex6 :
  ("x" ::= 10) -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  eapply tran.
  - eapply Assign.
  - apply refl.
Qed.

Compute Env1 "n".

Example ex7 :
  ("x" ::= "n") -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  apply tran with (s2 := ("x" ::= 10)) (sigma2 := Env1).
  - eapply Assing_2.
    apply Var.
  - apply ex6.
Qed.

#[local] Hint Constructors StmtEval : d1.
#[local] Hint Constructors StmtEvalClosure : d1.

Example ex6' :
  ("x" ::= 10) -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  eauto with d1.
Qed.

Example ex7' :
  ("x" ::= "n") -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  eauto with d1.
Qed.

Example ex7'' :
  ("x" ::= "n") ;; ("x" ::= 11) -{ Env1 }>*[ skip ; update (update Env1 "x" 10) "x" 11].
Proof.
  eauto 10 with d1.
Qed.
