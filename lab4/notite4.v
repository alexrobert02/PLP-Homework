(* 

"n" ::= 10 ;;
"s" ::= 0 ;;
"i" ::= 0 ;;
while ("i" <' "n") {
  "i" ::= "i" +' "1" ;;
  "s" ::= "s" +' "i" ;;
}


*)


(* Expresii aritmetice

Exp ::= nat          (num)
      | string       (var)
      | Exp "+'" Exp (plus, left, mai putin prioritara decat inmultirea: 50)
      | Exp "*'" Exp (mul, left, mai prioritar decat adunarea: 40)

 *)

Require Import String.
Open Scope string_scope.

Check "abc".

Inductive AExp :=
| anum  : nat -> AExp
| avar  : string -> AExp
| aplus : AExp -> AExp -> AExp
| amul  : AExp -> AExp -> AExp.


Check (anum 10).
Check (avar "i").
Check (aplus (avar "i") (anum 1)).


(* Coercion *)
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.

Check (aplus "i" 1).

(* Notation *)
Notation "A +' B" := (aplus A B)
                       (left associativity,
                         at level 50).
Notation "A *' B" := (amul A B)
                       (left associativity,
                         at level 40).

Check ("i" +' 1).
Check ("i" *' "n" +' 3).

Set Printing Coercions.
Check ("i" *' "n" +' 3).
Unset Printing Coercions.
Set Printing All.
Check ("i" *' "n" +' 3).

Check ("i" +' "n" *' 3).
Unset Printing All.

Check ("i" +' "n" *' 3).


(* Expresii bool *)

(* 
BExp := btrue
      | bfalse
      | not BExp (at level 70) 
      | BExp &&' BExp (at level 80) 
      | AExp <' AExp  (at level 60)
      | AExp >' AExp  (at level 60)
 *)

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.


Check bnot (blessthan "a" "n").

Check band (bnot (blessthan "a" "n"))
      (blessthan "i" 6).

(* ! "a" <' "n" &&' "i" <' 6 *)


Notation "! A" := (bnot A) (at level 70).
Notation "A <' B" := (blessthan A B) (at level 60).
Notation "A >' B" := (bgreaterthan A B) (at level 60).
Infix "&&'" := band (at level 80).


Check ! "a" <' "n".
Check ! "a" >' "n".

Check ! "a" <' "n" &&' "i" <' 6.


(* 
Stmt := string "::=" AExp  (assign)
      | "while" BExp Stmt  (while)
      | Stmt ";;" Stmt     (seq, right) 
      | ite BExp Stmt Stmt (ite)
      | skip               (skip)
 *)


Inductive Stmt :=
| assign : string -> AExp -> Stmt
| while  : BExp -> Stmt -> Stmt
| seq    : Stmt -> Stmt -> Stmt 
| ite    : BExp -> Stmt -> Stmt -> Stmt
| skip   : Stmt.


Check (assign "i" ("i" +' 1)).
Notation "X ::= V" := (assign X V) (at level 90).

Check "i" ::= "i" +' 1.


Check seq ( "i" ::= "i" +' "1")
      ("s" ::= "s" +' "i").
Notation "S1 ;; S2" := (seq S1 S2) (at level 99).

Check  "i" ::= "i" +' "1" ;;
               "s" ::= "s" +' "i".

Check "n" ::= 10 ;;
      "s" ::= 0 ;;
      "i" ::= 0 ;;
      while ("i" <' "n") (
         "i" ::= "i" +' "1" ;;
         "s" ::= "s" +' "i"
      ).
