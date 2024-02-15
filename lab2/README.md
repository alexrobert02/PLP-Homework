# Laborator 2

---
## Setup
Se vor considera cunoscute următoarele definiții:
```
Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.
```
---

## Exerciții de antrenament (testarea unor funcții):
* Se dă următoarea funcție de egalitate a două elemente de tip ```Nat```:
```
Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
  end.
```

Testați funcția ```eq_Nat``` rulând:
```
Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.
```

* Se dă funcția de adunare peste ```Nat```:
```
Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.
```

Testați funcția ```add``` rulând:
```
Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.
```

* Se dă o funcție ```max``` care returnează maximul dintre două elemente de tip ```Nat```:
```
Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.
```

Testați funcția ```max``` rulând:
```
Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.
```
---

## Exerciții propuse:
1. Scrieți o funcție ```le_Nat``` care primește doi parametri ```m``` și ```n``` de tip ```Nat``` și returnează ```true``` dacă ```m``` este mai mic sau egal decât ```n```.
```
Fixpoint le_Nat (m n : Nat) : bool :=
   ...
```

Testați funcția ```le_Nat``` pe următoarele exemple:
```
Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)
```

2. Demonstrați următoarea lemă (hint: puteți utiliza ```induction``` și ```inversion```):
```
Lemma le_then_O :
  forall n,
    le_Nat n O = true ->
    n = O.
Proof.
    ...
Qed.
```

3. Demonstrați următoarele leme prin inducție:
```
Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
    ...
Qed.
Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
    ...
Qed.
```

4. Demonstrați următoarea lemă prin inducție:
```
Lemma le_add :
  forall x y,
    le_Nat x (add x y) = true.
Proof.
  ....
Qed.
```

5. Demonstrați următoarea lemă:
```
Lemma le_add_consistent :
  forall m n k,
    le_Nat m n = true ->
    le_Nat m (add n k) = true.
Proof.
    ...
Qed.  
```

6. Demonstrați următoarea lemă:
```
Lemma le_max_true :
  forall m n,
    le_Nat m n = true ->
    max m n = n.
Proof.
    ...
Qed.
```

7. Demonstrați următoarea lemă:
```
Lemma le_max_false :
  forall m n,
    le_Nat m n = false ->
    max m n = m.
Proof.
  ...
Qed.
```
---