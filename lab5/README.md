# Laborator 5
* #### Semantica limbajelor de programare
---

## Exerciții de antrenament:

* Definiți un *environment* ```Env``` de tip ```string -> nat``` și o funcție ```update``` care actualizează valoarea unei variable de tip ```string``` cu o valoare de tipul ```nat```. Testați funcția ```update``` pe câteva exemple.


* Consultați tipul [option](https://coq.inria.fr/doc/V8.19.0/stdlib/Coq.Init.Datatypes.html#option) din documentația oficială. Citiți cu atenție definiția tipului.
---
## Exerciții propuse:

1. Definiți un interpretor pentru expresiile aritmetice și booleene definite mai jos:
```
Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| band : Cond -> Cond -> Cond.
```

Atenție la operațiile de scădere și împărțire: acestea pot produce erori. De aceea, un evaluator pentru expresii aritmetice va returna tipul ```option nat``` în loc de ```nat```. Pentru detalii despre ```option``` puteți rula pe rând comenzile:
```
Check option.
Check option nat.
Print option.
Check (Some 2).
Check None.
```

2. Definiți un interpretor pentru instrucțiunile definite mai jos:
```
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.
```

3. Scrieți un program care calculează cel mai mare divizor comun a două numere utilizând algoritmul lui Euclid prin scăderi repetate. Testați programul utilizând interpretorul definit la Exercițiul 2.


4. Scrieți un program care calculează cel de-al ```n```-lea termen al șirului Fibonacci. Testați programul utilizând interpretorul definit la Exercițiul 2.
---