# Laborator 7
* #### Small-step SOS
---

## Exerciții propuse:
1. Definiți o semantică Small-step pentru expresiile (aritmetice și booleene) definite mai jos și scrieți câte un exemplu simplu de derivare pentru fiecare tip de expresie:
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

```Nat.sub``` și ```Nat.div``` (din modulul ```Nat``` predefinite în Coq) pot fi utilizate pentru operațiile de scădere și înmulțire.

2. Definiți o semantică Small-step SOS pentru instrucțiunile definite mai jos și scrieți câte un exemplu simplu de derivare pentru fiecare instrucțiune:
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