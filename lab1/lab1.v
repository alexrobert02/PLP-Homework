Import Coq.Init.Nat.


(* 1. *)

Inductive Day :=
 | Monday
 | Tuesday
 | Wednesday
 | Thursday
 | Friday
 | Saturday
 | Sunday.


(* 2. *)

Definition eq (d1 d2 : Day) : bool :=
   match d1, d2 with
 | Monday, Monday => true
 | Tuesday, Tuesday => true
 | Wednesday, Wednesday => true
 | Thursday, Thursday => true
 | Friday, Friday => true
 | Saturday, Saturday => true
 | Sunday, Sunday => true
 |  _, _ => false
  end.


(* 3. *)

Definition next_day (d:Day) : Day :=
  match d with
  | Monday => Tuesday
  | Tuesday => Wednesday
  | Wednesday => Thursday
  | Thursday => Friday
  | Friday => Saturday
  | Saturday => Sunday
  | Sunday => Monday
  end.

Compute next_day (Friday).


(* 4. *)

Inductive Bool :=
 | True
 | False.


(* 5. *)

Definition negation (b:Bool) : Bool :=
  match b with
  | True => False
  | False => True
  end.

Compute negation (True).

Definition conjunction (b1 b2 : Bool) : Bool :=
  match b1, b2 with
  | True, True => True
  | True, False => False
  | False, True => False
  | False, False => False
  end.

Compute conjunction (True) (False).

Definition disjunction (b1 b2 : Bool) : Bool :=
  match b1, b2 with
  | True, True => True
  | True, False => True
  | False, True => True
  | False, False => False
  end.

Compute disjunction (False) (True).


(* 6. *)

Inductive Byte :=
  byte : bool -> bool -> bool -> 
         bool -> bool -> bool ->
         bool -> bool -> Byte.

Check byte false false false false
      true false false false.

Check byte false false false false false
      false false true.

Check eqb.
Compute eqb 2 3.
Compute eqb 2 2.

Definition eight :=  byte false false false false true false false false.

Definition one := byte false false false false false false false false.

Definition extract_bit (i : nat) (b : Byte) : bool :=
  match b with
  | byte b7 b6 b5 b4 b3 b2 b1 b0 =>
      if (eqb i 0)
      then b0
      else if (eqb i 1)
           then b1
           else if (eqb i 2)
                then b2
                else if (eqb i 3)
                     then b3
                     else if (eqb i 4)
                           then b4
                           else if (eqb i 5)
                                then b5
                                else if (eqb i 6)
                                     then b6
                                     else if (eqb i 7)
                                          then b7
                                          else false
  end.

Compute extract_bit 1 one.
Compute extract_bit 0 one.
Compute extract_bit 3 eight.
Compute extract_bit 10 one.

Check xorb.

Definition add_bit (bit1 bit2 : bool) : bool :=
  (xorb bit1 bit2).

Compute add_bit false false.
Compute add_bit false true.
Compute add_bit true false.
Compute add_bit true true.

Definition carry (bit1 bit2 c : bool) : bool :=
  match bit1, bit2, c with
  | true, true, _ => true
  | true, _, true => true
  | _, true, true => true
  | _, _, _       => false
  end.

Compute carry true true true.
Compute carry false true true.
Compute carry true false false.

Definition add (b1 b2 : Byte) : Byte :=
  match b1, b2 with
  | byte a7 a6 a5 a4 a3 a2 a1 a0,
    byte b7 b6 b5 b4 b3 b2 b1 b0 =>
      let s0 := (add_bit a0 b0) in
      let c0 := (carry a0 b0 false) in
      let s1 := add_bit (add_bit a1 b1) c0 in
      let c1 := (carry a1 b1 c0) in
      let s2 := add_bit (add_bit a2 b2) c1 in
      let c2 := (carry a2 b2 c1) in
      let s3 := add_bit (add_bit a3 b3) c2 in
      let c3 := (carry a3 b3 c2) in
      let s4 := add_bit (add_bit a4 b4) c3 in
      let c4 := (carry a4 b4 c3) in
      let s5 := add_bit (add_bit a5 b5) c4 in
      let c5 := (carry a5 b5 c4) in
      let s6 := add_bit (add_bit a6 b6) c5 in
      let c6 := (carry a6 b6 c5) in
      let s7 := add_bit (add_bit a7 b7) c6 in
      let c7 := (carry a7 b7 c6) in

      byte s7 s6 s5 s4 s3 s2 s1 s0
  end.

Compute add eight one.

Check pow.
Compute pow 2 7.

Definition pow_extract (i : nat) (b:Byte) : nat :=
  if (extract_bit i b)
  then pow 2 i
  else 0.

Definition to_nat (b: Byte) : nat :=
  pow_extract 7 b +
  pow_extract 6 b +
  pow_extract 5 b +
  pow_extract 4 b +
  pow_extract 3 b +
  pow_extract 2 b +
  pow_extract 1 b +
  pow_extract 0 b.

Compute to_nat eight.
Compute to_nat one.

Definition max := byte true true true true true true true true.

Compute to_nat max.

Compute to_nat (add eight one).