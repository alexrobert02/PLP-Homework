Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)


Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".


(* 1. *)

Inductive Exp : Type :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.

Notation "A +' B" := (add A B)
                       (left associativity,
                         at level 50).

Notation "A -' B" := (sub A B)
                       (left associativity,
                         at level 50).

Notation "A /' B" := (div A B)
                       (left associativity,
                         at level 40).

Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add 2 (add "x" (div 2 "y"))).

Set Printing Coercions.
Check (add 2 (add "x" (div 2 "y"))).
Unset Printing Coercions.

Check 2 +' ("x" +' 2 /' "y").
Set Printing All.
Check 2 -' ("x" +' 2 /' "y").
Check 2 -' "x" /' "y".
Check "x" /' "y" +' 2.
Check "x" /' "y" /' "z".
Unset Printing All.


(* 2. *)

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
Notation "A |' B" := (bnot (band (bnot A) (bnot B))) (at level 80).
Notation "A >' B" := (band (bnot (less A B)) (bnot (beq A B))) (at level 60).
Notation "A >=' B" := (bnot (less A B)) (at level 70).
Notation "A <=' B" := (bnot (band (bnot (less A B)) (bnot (beq A B)))) (at level 70).

Check "x" <' "y".
Check "x" =' "y".
Check ! "x" =' "y".
Check "x" <' "y" &' "x" =' "y".
Check "x" <' "y" |' "x" =' "y".
Check "x" >' "y" |' "x" =' "y".
Check "x" >' "y".
Check 2 >' "y".
Check 3 >' "y".
Check "x" <=' "y".
Check 3 <=' "y".
Check 2 <=' "y".
Check "x" >=' "y".
Check 2 >=' "y".
Check 1 >=' "y".
Check !(! "x" <' "y" &' ! "x" =' "y").
Check ("x" <' "y" |' "x" =' "y") .


(* 3. *)

Inductive Stmt :=
| skip : Stmt
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt.

Notation "X ::= V" := (assign X V) (at level 90).
Notation "S1 ;; S2" := (seq S1 S2) (at level 99).


(* 4. *)

Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;;
   while (x >' y) (
      x ::= x -' y
   );;
   ite (x =' y) ("m" ::= 0) ("m" ::= x) ;;
   "result" ::= "m".

Definition is_even (x : string) :=
  ite (x /' 2 =' 0) ("is_even" ::= 1) ("is_even" ::= 0).


(* 5. *)

Definition cmmdc (x y : string) :=
  while (! x =' y) (
    ite (x >' y) (x ::= x -' y) (y ::= y -' x)
  ) ;;
  
  "result" ::= x.


(* 6. *)

Definition fib (n : string) :=
    "a" ::= 0 ;;
    "b" ::= 1 ;;
    "i" ::= 1 ;;
    while ("i" <' n) (
      "c" ::= "a" +' "b" ;;
      "a" ::= "b" ;;
      "b" ::= "c"
    );;
    "result" ::= "b".
