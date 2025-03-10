Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : ltb 1 1 = false).
Check (eq_refl false <: ltb 1 1 = false).
Check (eq_refl false <<: ltb 1 1 = false).
Definition compute1 := Eval compute in ltb 1 1.
Check (eq_refl compute1 : false = false).

Check (eq_refl : ltb 1 2 = true).
Check (eq_refl true <: ltb 1 2 = true).
Check (eq_refl true <<: ltb 1 2 = true).
Definition compute2 := Eval compute in ltb 1 2.
Check (eq_refl compute2 : true = true).

Check (eq_refl : ltb 9223372036854775807 0 = false).
Check (eq_refl false <: ltb 9223372036854775807 0 = false).
Check (eq_refl false <<: ltb 9223372036854775807 0 = false).
Definition compute3 := Eval compute in ltb 9223372036854775807 0.
Check (eq_refl compute3 : false = false).
