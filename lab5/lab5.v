Require Import String.
Open Scope string_scope.


Definition Env := string -> option nat.
Definition env (string : string) :=
if (string_dec string "n")
  then Some 10
  else None.

Definition update (env : Env) (var : string) (val : option nat) : Env :=
  fun y => if eqb y var
           then val
           else (env y).


(* 1. *)

Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
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
                       (left associativity,
                         at level 40).

Fixpoint ExpEval (a : Exp) (env : Env) : option nat :=
  match a with
  | num n => Some n
  | var x => env x
  | add a1 a2 => match (ExpEval a1 env) with
                 | None => None
                 | Some a1 => match (ExpEval a2 env) with
                              | None => None
                              | Some a2 => Some (a1 + a2)
                              end
                 end
  | sub a1 a2 => match (ExpEval a1 env) with
                 | None => None
                 | Some a1 => match (ExpEval a2 env) with
                              | None => None
                              | Some a2 => if (Nat.leb a1 a2)
                                           then None
                                           else Some (a1 - a2)
                              end
                 end
  | div a1 a2 => match (ExpEval a1 env) with
                 | None => None
                 | Some a1 => match (ExpEval a2 env) with
                              | None => None
                              | Some a2 => if (Nat.eqb a2 0)
                                           then None
                                           else Some (Nat.div a1 a2)
                              end
                 end
  end.

Compute ExpEval (13 /' 4) env.
Compute ExpEval (13 /' 0) env.
Compute ExpEval (4 -' 3) env.
Compute ExpEval (1 -' 3) env.
Compute ExpEval (2 +' 5 -' 6) env.
Compute ExpEval (2 +' 5 /' 5) env.

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

Fixpoint CondEval (b : Cond) (env : Env) : bool :=
  match b with
  | base b => b
  | bnot b => negb (CondEval b env)
  | beq a1 a2 => match (ExpEval a1 env) with
                 | None => false
                 | Some a1 => match (ExpEval a2 env) with
                              | None => false
                              | Some a2 => if (Nat.eqb a1 a2)
                                           then true
                                           else false 
                              end
                 end
  | less a1 a2 => match (ExpEval a1 env) with
                  | None => false
                  | Some a1 => match (ExpEval a2 env) with
                               | None => false
                               | Some a2 => if Nat.ltb a1 a2
                                            then true
                                            else false 
                               end
                  end
  | band b1 b2 => andb (CondEval b1 env) (CondEval b2 env)
  end.

Compute CondEval (50 =' 50) env.
Compute CondEval (2 <' "n") env.
Compute CondEval (! 4 =' 4) env.


(* 2. *)

Inductive Stmt :=
| skip : Stmt
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| it  : Cond -> Stmt -> Stmt
| dowhile : Stmt -> Cond -> Stmt.

Fixpoint StmtEval (s : Stmt) (env: Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' => match s with
              | skip => env
              | assign x a => update env x (ExpEval a env)
              | seq s1 s2 => StmtEval s2 (StmtEval s1 env gas') gas'
              | ite b s1 s2 => if (CondEval b env)
                               then StmtEval s1 env gas'
                               else StmtEval s2 env gas'
              | dowhile s b => if (CondEval b (StmtEval s env gas'))
                               then StmtEval (dowhile s b) (StmtEval s env gas') gas'
                               else StmtEval s env gas'
              | it b s1 => if (CondEval b env)
                               then StmtEval s1 env gas'
                               else env
              end
  end.
   
Notation "X ::= V" := (assign X V) (at level 85).
Notation "S1 ;; S2" := (seq S1 S2) (right associativity, at level 99).


(* 3. *)

Compute (StmtEval
            ("x" ::= 15 ;;
             "y" ::= 25 ;;
             dowhile
                (ite ("x" <' "y") 
                   ("y" ::= "y" -' "x")
                   ("x" ::= "x" -' "y"))
             (!"x" =' "y"))
         env 100) "x".


(* 4. *)

Compute (StmtEval
            ("a" ::= 0 ;;
             "b" ::= 1 ;;
             "i" ::= 1 ;;
             "n" ::= 8 ;;
             dowhile
                 ("c" ::= "a" +' "b" ;;
                  "a" ::= "b" ;;
                  "b" ::= "c" ;;
                  "i" ::= "i" +' 1)
             ("i" <' "n"))
         env 100) "b".
