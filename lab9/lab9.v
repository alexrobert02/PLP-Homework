Require Import String.
Require Import List.
Import ListNotations.


Inductive B :=
| T : B
| F : B
| neg : B -> B
| and : B -> B -> B
| or  : B -> B -> B.


(* 1. *)

Fixpoint interpret (b : B) : bool :=
  match b with
  | T => true
  | F => false
  | neg b' => match interpret b' with
              | true => false
              | false => true
              end
  | and b1 b2 => match (interpret b1, interpret b2) with
                 | (true, true) => true
                 | _ => false
                 end
  | or b1 b2 => match (interpret b1, interpret b2) with
                | (false, false) => false
                | _ => true
                end
  end.