Require Import String.
Open Scope string_scope.

(* mapping string |-> nat *)

Definition Env0 : string -> nat :=
  fun x => if eqb x "n"
           then 10
           else 0.

Check Env0.

Compute Env0 "n".
Compute Env0 "m".

Definition update
           (env : string -> nat)
           (x   : string)
           (v   : nat) :
  (string -> nat) :=

  fun y => if eqb y x
           then v
           else (env y).


Compute Env0 "n".

Definition Env1 := update Env0 "n" 100.

Compute Env1 "n".

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



Check (2 +' 4 *' 6).

Check (2 +' "n" *' 6).


Fixpoint aeval
         (a : AExp)
         (env : string -> nat) : nat :=
  match a with
  | var x => env x
  | num n => n
  | plus a1 a2 => (aeval a1 env) +
                    (aeval a2 env)
  | mult a1 a2 => (aeval a1 env) *
                    (aeval a2 env)
  end.

Compute aeval (2 +' "n" *' 6) Env0.
Compute aeval (2 +' "n" *' 6) Env1.


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


Check (! 2 <' "n").
Check (! 2 <' "n") &&' 2 >' "n".
Check (! 10 <' "n") &&' 102 >' "n".
Check negb.

Locate "<".
Check lt.

Compute lt 2 4.

Check Nat.ltb.

Compute Nat.ltb 2 2.

Locate ">".
Compute negb (Nat.leb 2 3).

Fixpoint beval
         (b : BExp)
         (env : string -> nat)
  : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | bnot b1 => negb (beval b1 env)
  | band b1 b2 =>
      andb
        (beval b1 env)
        (beval b2 env)
  | blessthan a1 a2 =>
      Nat.ltb
        (aeval a1 env)
        (aeval a2 env)
  | bgreaterthan a1 a2 =>
      negb (Nat.leb 
              (aeval a1 env)
              (aeval a2 env))
  end.


Compute beval (! 2 <' "n") Env0.
Compute beval (!! 2 <' "n") Env0.

Compute beval ((! 2 <' "n") &&' 2 >' "n") Env0.
Compute beval ((!! 2 <' "n") &&' 2 >' "n") Env0.

Compute beval ((!! 2 <' "n") &&' ! 2 >' "n") Env0.


Compute beval ((! 10 <' "n") &&' 102 >' "n") Env0.



(* Statements *)
Inductive Stmt :=
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt
| assign : string -> AExp -> Stmt
| while : BExp -> Stmt -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt.

Notation "S1 ;; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Check "n" ::= 10.

Check "n" ::= 10 ;;
      "i" ::= 0.


Check "n" ::= 10 ;; "m" ::= 20 ;;
       (ite ("n" >' "m")
         ("max" ::= "n")                                ("max" ::= "m")).

Check "n" ::= 10 ;;
      "i" ::= 0 ;;
      "s" ::= 0 ;;
      while ("i" <' "n") (
              "i" ::= "i" +' 1;;
              "s" ::= "s" +' "i"
            ).


Fixpoint eval
         (S : Stmt)
         (env : string -> nat)
         (gas : nat)
  : string -> nat :=
  match gas with
  | O      => env
  | S gas' => match S with
              | skip => env
              | assign x a => update env x (aeval a env)
              | seq s1 s2 => eval s2 (eval s1 env gas') gas'
              | ite b s1 s2 => if (beval b env)
                               then (eval s1 env gas')
                               else (eval s2 env gas')
              | while b s => if (beval b env)
                             then eval (while b s) (eval s env gas') gas'
                             else env
              end
  end.
  

Compute (eval skip Env0 10) "n".
Compute (eval ("n" ::= 11) Env0 10) "x".
Compute (eval
           ("n" ::= 10 ;;
            "i" ::= 100
           )
           Env0 10) "i".


Compute (eval
           ("n" ::= 10 ;; "m" ::= 20 ;;
             (ite ("n" >' "m")
                  ("max" ::= "n")                                   ("max" ::= "m")))
           Env0 4) "max".

Compute (eval
           ("n" ::= 30 ;; "m" ::= 20 ;;
             (ite ("n" >' "m")
                  ("max" ::= "n")                                   ("max" ::= "m")))
           Env0 10) "max".


Compute (eval
           (
      "n" ::= 10 ;;
      "i" ::= 0 ;;
      "s" ::= 0 ;;
      while ("i" <' "n") (
              "i" ::= "i" +' 1;;
              "s" ::= "s" +' "i"
            ))
           Env0
           100) "s".