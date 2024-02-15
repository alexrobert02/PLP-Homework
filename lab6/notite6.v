Require Import String.
Open Scope string_scope.

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

(* arithmetic expressions *)
Inductive AExp :=
| var : string -> AExp
| num : nat -> AExp
| plus : AExp -> AExp -> AExp
| mult : AExp -> AExp -> AExp.

Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.
Notation "A +' B" := (plus A B)
                      (at level 50,
                        left associativity).

Notation "A *' B" := (mult A B)
                      (at level 40,
                        left associativity).


(* 

                   .
Const --------------------------
       < i , sigma > => < i >

                   .
Var  --------------------------
       < x , sigma > => < sigma(x) >

      <a1, sigma> => i1   <a2, sigma> => i2 
Plus ---------------------------------------
        <a1 +' a2, sigma> => <i1 + i2>

      <a1, sigma> => i1   <a2, sigma> => i2 
Mult ---------------------------------------
        <a1 *' a2, sigma> => <i1 * i2>

*)

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| Const : forall i sigma, num i =[sigma]=> i
| Var : forall x sigma, var x =[sigma]=> sigma x
| Plus: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma]=> i1 ->
  a2 =[sigma]=> i2 ->
  n  = i1 + i2 ->
  a1 +' a2 =[sigma]=> n
| Mult: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma]=> i1 ->
  a2 =[sigma]=> i2 ->
  n  = i1 * i2 ->
  a1 *' a2 =[sigma]=> n
where "A =[ S ]=> N" := (aeval A S N).

Definition Env1 := update (fun x => 0) "n" 10.
Compute Env1 "n".

Example aeval1:
  2 +' "n" =[ Env1 ]=> 2 + 10.
Proof.
  (* v1:
  apply Plus with (i1 := 2) (i2 := 10).
   *)
  eapply Plus.
  - apply Const.
  - apply Var.
  - reflexivity.
Qed.

Example aeval2:
  2 +' "n" =[ Env1 ]=> 12.
Proof.
  eapply Plus with (i1 := 2).
  - apply Const.
  - apply Var.
  - unfold Env1. unfold update.
    simpl.
    reflexivity.
Qed.

Create HintDb mydb.
#[local] Hint Constructors aeval : mydb.
#[local] Hint Unfold Env1 : mydb.
#[local] Hint Unfold update : mydb.

Example aeval2':
  2 +' "n" =[ Env1 ]=> 12.
Proof.
  eauto with mydb.
Qed.


(* boolean expressions *)
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.

Notation "! A" := (bnot A) (at level 70).
Notation "A &&' B" := (band A B) (at level 76, left associativity).
Notation "A <' B" := (blessthan A B) (at level 65).
Notation "A >' B" := (bgreaterthan A B) (at level 65).

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90).

Print BExp.

Inductive beval :
  BExp -> Env -> bool -> Prop :=
| T : forall sigma, btrue  ={ sigma }=> true
| F : forall sigma, bfalse ={ sigma }=> false
| NotT : forall B sigma,
    B ={ sigma }=> true ->
    bnot B ={ sigma }=> false 
| NotF : forall B sigma,
    B ={ sigma }=> false ->
    bnot B ={ sigma }=> true
| AndT : forall b1 b2 sigma b,
   b1 ={ sigma }=> true ->
   b2 ={ sigma }=> b ->
   b1 &&' b2 ={ sigma }=> b
| AndF : forall b1 b2 sigma,
   b1 ={ sigma }=> false ->
   b1 &&' b2 ={ sigma }=> false
| Lt : forall a1 a2 i1 i2 b sigma, 
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b  = Nat.ltb i1 i2 ->
  a1 <' a2 ={ sigma }=> b 
| Gt : forall a1 a2 i1 i2 b sigma, 
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b  = negb (Nat.leb i1 i2) ->
  a1 >' a2 ={ sigma }=> b 
where "B ={ Sigma }=> B'" := (beval B Sigma B').

#[local] Hint Constructors beval : mydb.

Example beval1:
  2 +' "n" <' 13 ={ Env1 }=> true.
Proof.
  eauto with mydb.
  (* eapply Lt with (i2 := 13). *)
  (* - eapply aeval2. *)
  (* - apply Const. *)
  (* - eauto with mydb. *)
Qed.

(* Statements *)
Inductive Stmt :=
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "S1 ;; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Reserved Notation "S1 -[ Sigma ]-> Sigma'"
         (at level 99).

Inductive eval : Stmt -> Env -> Env -> Prop :=
| Assign: forall a i sigma x sigma',
  a =[ sigma ]=> i ->
  sigma' = update sigma x i ->  
  (x ::= a) -[ sigma ]-> sigma'
| Seq : forall s1 s2 sigma sigma0 sigma',
  s1 -[ sigma ]-> sigma0 ->
  s2 -[ sigma0]-> sigma' ->
  (s1 ;; s2) -[ sigma ]-> sigma'
| WhileF : forall b sigma s,
  b ={ sigma }=> false ->
  (while b s) -[ sigma ]-> sigma
| WhileT : forall b sigma s sigma',
  b ={ sigma }=> true ->
  (s ;; while b s) -[ sigma ]-> sigma' ->
  (while b s) -[ sigma ]-> sigma'
where "S1 -[ Sigma ]-> Sigma'" := (eval S1 Sigma Sigma').


#[local] Hint Constructors eval : mydb.

Example eval1:
  exists Env2, 
    ("n" ::= 100 -[ Env1 ]-> Env2) /\
      (Env2 = update Env1 "n" 100).
Proof.
  eexists.
  split.
  - eapply Assign.
    + apply Const.
    + reflexivity.
  - reflexivity.
Qed.


Example eval1':
  exists Env2, 
    ("n" ::= 100 -[ Env1 ]-> Env2) /\
      (Env2 = update Env1 "n" 100).
Proof.
  eauto with mydb.
Qed.

Example eval3:
  ("n" ::= 0 ;;
  while ("n" <' 1) ( "n" ::= "n" +' 1))
  -[ Env1 ]-> update (update Env1 "n" 0) "n" 1.
Proof.
  eauto 10 with mydb.
Qed. 