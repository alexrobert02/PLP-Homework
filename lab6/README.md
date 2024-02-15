# Laborator 6
* #### Big-step SOS
---

## Exerciții propuse:
1. Definiți o semantică Big-step pentru expresiile (aritmetice și booleene) definite mai jos și scrieți câte un exemplu simplu de derivare pentru fiecare tip de expresie:
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

Pentru a evita situațiile în care implementarea Coq devine prea complexă, vom utiliza funcțiile ```Nat.sub``` și ```Nat.div``` (din modulul ```Nat``` predefinit în Coq) pentru operațiile de scădere și împărțire. În acest laborator este important să înțelegem care sunt și cum se aplică regulile Big-step.


2. Definiți o semantică Big-step SOS pentru instrucțiunile definite mai jos și scrieți câte un exemplu simplu de derivare pentru fiecare instrucțiune:
```
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.
```
---