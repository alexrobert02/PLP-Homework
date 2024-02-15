Module TM.
From Coq Require Import Unicode.Utf8.


(* 1. *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'" := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'" := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'" := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

Inductive bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t /\ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').
Hint Constructors step : core.


(* 2. *)

(*=============================================================
         .
TZero -------
      O : Nat
===============================================================
       t : Nat
TSucc ---------
      S t : Nat
===============================================================
           .
TTrue -----------
      true : Bool
===============================================================
            .
TFalse -----------
       true : Bool
===============================================================
    t1 : Bool   t2 : T   t3 : T
TIf ---------------------------
     if t1 then t2 else t3 : T
===============================================================
       e : Nat
TPred ---------
      S e : Nat
===============================================================
            t1 : Nat    
TIszero ----------------
        iszero t1 : Bool
=============================================================*)


(* 3. *)

(*=============================================================
           .                                      .
        -------                                -------
        O : Nat                                O : Nat
     -------------                          -------------
     succ(O) : Nat            .             succ(O) : Nat
----------------------  ------------  -------------------------
iszero(succ(O)) : Bool  false : Bool  pred(succ(succ(O))) : Nat
---------------------------------------------------------------
        if iszero(succ(O)) then false else pred(succ(O))
===============================================================
        .                            .
     -------                      -------
     O : Nat                      O : Nat
----------------  -----------  -------------
iszero(O) : Bool  true : Bool  succ(O) : Nat
--------------------------------------------
    if iszero(O) then true else succ(O)
=============================================================*)


(* 4. *)

Reserved Notation "t '∈' T" (at level 40).

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Declare Scope tm_scope.

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
        <{ true }> ∈ Bool
  | T_False :
        <{ false }> ∈ Bool
  | T_If : forall t1 t2 t3 T,
        t1 ∈ Bool ->
        t2 ∈ T ->
        t3 ∈ T ->
        <{ if t1 then t2 else t3 }> ∈ T
  | T_0 :
        <{ 0 }> ∈ Nat
  | T_Succ : forall t1,
        t1 ∈ Nat ->
        <{ succ t1 }> ∈ Nat
  | T_Pred : forall t1,
        t1 ∈ Nat ->
        <{ pred t1 }> ∈ Nat
  | T_Iszero : forall t1,
        t1 ∈ Nat ->
        <{ iszero t1 }> ∈ Bool
where "t '∈' T" := (has_type t T).
