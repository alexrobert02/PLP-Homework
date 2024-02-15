# Laborator 8
* #### Type systems
---

## Exerciții propuse:
Se consideră cunoscută următoarea sintaxa BNF a unui limbaj de expresii:
```
E ::= 'O' | 'S' E | 'isZero' E | 'T' | 'F' | 'ite' E E E
```

1. Definiți o semantică Small-Step pentru expresiile de mai sus.


2. Scrieți (în ASCII) regulile de tipizare pentru expresiile de mai sus.\
Exemplu:
```
            .
TZero ------------
           O : Nat

           e : Nat
TSucc -------------
          S e : Nat
```

3. Scrieți (în ASCII, ca mai sus) 2 exemple de derivări care utilizează regulile de tipizare pe care le-ați definit la exercițiul 2. Cele 2 exemple trebuie să acopere toate construcțiile limbajului de expresii.


4. Implementați regulile de la exercițiul 2 în Coq și testați implementarea pe exemplele de la exercițiul 3 (fără a folosi ```eauto```).
---