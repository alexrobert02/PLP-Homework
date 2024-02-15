Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.

(* Expressions *)
Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| plus : Exp -> Exp -> Exp
| mult : Exp -> Exp -> Exp.


Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.
Notation "A +' B" := (plus A B)
                       (at level 50,
                         left associativity).
Notation "A *' B" := (mult A B)
                       (at level 40,
                         left associativity).

Definition Env := string -> nat.

Fixpoint interpret
         (e : Exp)
         (sigma : Env) : nat :=
  match e with
  | num n => n
  | var x => (sigma x)
  | plus e1 e2 => (interpret e1 sigma)
                  + (interpret e2 sigma)
  | mult e1 e2 => (interpret e1 sigma)
                  * (interpret e2 sigma)
  end.

Definition sigma1 : Env := fun x => 1.

Compute interpret (2 +' "n") sigma1.
Compute interpret (2 *' "n") sigma1.


(* Stack machine *)
Print list.
Check list nat.

Check nil.
Check (cons 2 nil).
Check (cons 3 (cons 2 nil)).

Check [3;2;1].
Definition stack1 := [3;2;1].
Compute (4::stack1).
Compute [2;3] ++ [4;5].
Check app.
Compute app [2;3] [4;5].

Definition Stack := list nat.

Inductive Instruction :=
| push_const : nat -> Instruction
| push_var : string -> Instruction
| add : Instruction
| mul : Instruction.

Check [push_const 2;
       push_var "n";
       mul].

Definition run_instruction
         (i : Instruction)
         (stack : Stack)
         (sigma : Env) : Stack :=
  match i with
  | push_const n => n :: stack 
  | push_var x => (sigma x) :: stack 
  | add => match stack with
           | (n1 :: n2 :: stack') => (n1 + n2)::stack'
           | _ => stack
           end
  | mul => match stack with
           | (n1 :: n2 :: stack') => (n1 * n2)::stack'
           | _ => stack
           end
  end.

Compute run_instruction add [2;1] sigma1.
Compute run_instruction add [3;2;1] sigma1.

Fixpoint run_instructions
         (instrs : list Instruction)
         (stack : Stack)
         (sigma : Env) : Stack :=
  match instrs with
  | [] => stack
  | i :: is' =>
      run_instructions is'
                       (run_instruction i stack sigma)
                       sigma
  end.


Compute run_instructions
        [push_const 2; push_var "n"; mul]
        []
        sigma1.
Compute interpret (2 *' "n") sigma1.


(* Compiler *)
Fixpoint compile (e : Exp) : list Instruction :=
  match e with
  | num n => [push_const n]
  | var x => [push_var x]
  | plus e1 e2 => (compile e2) ++ (compile e1) ++ [add]
  | mult e1 e2 => (compile e2) ++ (compile e1) ++ [mul]
  end.

Compute compile (2 *' "n").

Compute compile (2 +' "n" *' 4).
Compute compile (2 *' "n" +' 4).

Compute interpret (2 *' "n" +' 4) sigma1.
Compute run_instructions
        (compile (2 *' "n" +' 4))
        []
        sigma1.


Lemma soundness_helper:
 forall e instrs stack sigma,
   run_instructions ((compile e) ++ instrs) stack sigma =
     run_instructions instrs ((interpret e sigma) :: stack) sigma.
Proof.
  induction e; intros; trivial; simpl.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
Qed.

(* Soundness *)
Theorem soundness:
  forall e sigma,
    run_instructions (compile e) [] sigma =
      [interpret e sigma].
Proof.
  intros e sigma.
  rewrite <- app_nil_r
    with (l := (compile e)).
  rewrite soundness_helper.
  simpl.
  reflexivity.
Qed.