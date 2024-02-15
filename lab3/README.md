# Laborator 3
* #### Tactics [CheatSheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html)
---
## Exerciții propuse:
1. Definiți o un tip de date polimorfic pentru arbori binari.


2. Definiți o funcție ```mirror``` care oglindește un arbore binar (al cărui tip a fost definit la exercițiul precendent).


3. Demonstrați că funcția mirror este convolutivă (eng. *convolutive*), adică ```mirror (mirror t) = t``` pentru orice arbore binar ```t```.


4. Scrieți o funcție de nivel superior denumită ```process``` care primește o funcție de tip ```f : T -> T``` și un arbore binar parametric în tipul ```T``` și aplică funcția ```f``` fiecărui nod din arbore. Testați funcția ```process``` utilizând funcții anonime trimise ca parametru.


5. Demonstrați următoarele teoreme:
```
Theorem and_elim_1:
  forall (A B : Prop), A /\ B -> A.
Admitted.
```

```
Theorem and_elim_2:
  forall (A B : Prop), A /\ B -> B.
Admitted.
```

```
Theorem and_intro:
  forall (A B : Prop), A -> B -> (A /\ B).
Admitted.
```

```
Theorem or_elim:
  forall (A B C: Prop), (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
Admitted.
```

```
Theorem or_intro_1:
  forall (A B : Prop), A -> (A \/ B).
Proof.
Admitted.
```

```
Theorem or_intro_2:
  forall (A B : Prop), B -> (A \/ B).
Proof.
Admitted.
```

```
Theorem not_not:
  forall (P : Prop), P -> ~~P.
Proof.
Admitted.
```

```
Theorem mp :
  forall A B,
    (A -> B) -> A -> B.
Proof.
Admitted.
```

```
Theorem mt :
  forall (A B : Prop),
    (A -> B) -> ~ B -> ~ A.
Proof.
```
---
