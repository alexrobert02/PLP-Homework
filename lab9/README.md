# Laborator 9
* #### Compilation
---

## Exerciții propuse:
În acest laborator vom lucra cu un limbaj ```B``` pentru expresii booleene care va conține constantele ```T``` și ```F``` (corespunzatoare valorilor *true* și respectiv *false*) și operațiile: negație, conjuncție și disjuncție. Sintaxa abstractă este definită mai jos:
```
Require Import String.
Require Import List.
Import ListNotations.

Inductive B :=
| T : B
| F : B
| neg : B -> B
| and : B -> B -> B
| or  : B -> B -> B.
```

1. Definiți un interpretor pentru limbajul B, completând codul de mai jos în spațiile goale (```...```):
```
Fixpoint interpret (b : B) : bool :=
  match b with
  | T => true
  | F => ...
  | neg b => ...
  | and b1 b2 => ...
  | or b1 b2 => ...
  end.
```

2. Se consideră definiția unui *stack machine* de mai jos:
```
Inductive Instruction :=
| push : nat -> Instruction
| inv : Instruction
| add : Instruction
| mul : Instruction.
```

Deși această mașină de calcul bazat pe stivă lucrează cu numere naturale, pe stivă vom utiliza **doar** valorile 0 și 1 (sau ```O``` și ```S O```). Motivul pentru care ne limităm la aceste valori este că vom vrea să definim un compilator pentru expresiile limbajului ```B``` în care valorile ```T``` și ```F``` să fie codificate cu ```1``` și respectiv ```0```. Mai mult, operațiile booleene conjuncție și disjuncție vor fi codificate utilizând operații peste numere naturale (```mul``` și respectiv ```add```), iar negația va fi codificată utilizând operația ```inv``` (care transformă ```1``` în ```0``` și invers). Așadar, definim următoarea semantică pentru instrucțiunea ```push```:
```
Fixpoint run_instruction (i : Instruction) (stack : list nat) : list nat :=
  match i with
  | push n => match n with
              | O => O :: stack
              | S n' => (S O) :: stack
              end
  | inv => ...
  | add => ...
  | mul => ...
  end.
```

```
Cerință: completați spațiile libere (...) din definiția de mai sus.
```

3. Completați funcția de mai jos care primește la intrare o listă instrucțiuni și o stivă și returnează stiva obținută în urma execuției instrucțiunilor:
```
Fixpoint run_instructions
         (stpgm : list Instruction)
         (stack : list nat) :=
  ...
```
Această funcție va apela funcția ```run_instruction``` de la exercițiul precedent.

4. Completați funcția de compilare de mai jos:
```
Fixpoint compile (b : B) : list Instruction :=
  match b with
    ...
  end.
```

5. Demonstrați următoarele proprietăți:
```
Lemma soundness_helper:
  forall b instrs stack,
    run_instructions ((compile b) ++ instrs) stack =
    run_instructions instrs (to_nat (interpret b) :: stack).
Proof.
Admitted.
```

```
Theorem soundness :
  forall b,
    run_instructions (compile b) nil =  [to_nat (interpret b)].
Proof.
Admitted.
```
---