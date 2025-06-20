Require Import PrimInt63 PrimFloat PrimString PrimArray.
CoInductive Stream (A : Type) :=
  Cons : A -> Stream A -> Stream A.

#[projections(primitive)]
Record BoxTrue := mkBoxTrue { boxI: True }.

Record MLB := mlb { lbI := I }.
Variant MagicHat: Set := hat: let x := I in MagicHat.

Symbol other_I : True.

Rewrite Rules unfold_I :=
| other_I => I
.

(* App, Const (primitive), and Int *)
Eval step cbv in (add 12 13)%uint63.
(* LetIn and Float *)
Eval step cbv in let x := 1%float in 1%float.
(* Array and Const (unfoldable) *)
Eval step cbv in [| Nat.add | Nat.add |].
(* Lambda and Sort *)
Eval step cbv in fun x => Set.
(* Case, Const (rule) and Construct *)
Eval step cbv in match other_I with I => I end.
(* Case w/ let bindings *)
Eval step cbv in match mlb with mlb x => x end.
Eval step cbv in match hat with hat x => x end.
(* Fix and String *)
Eval step cbv in fix f (x: True) := "a"%pstring.
Section Test.
    Variable z: Type.
    (* Cast and Var *)
    Eval step cbv in (z: Type).
End Test.
(* CoFix and Rel *)
Eval step cbv in cofix f (x: Stream True) := x.
(* Proj and Evar (no body) *)
Eval step cbv in _.(boxI).
(* Prod, Ind, and Evar (body) *)
Goal True.
refine (_ ?[x]).
[x]: refine (_ _).
step cbv.
Abort.
(* META are supposed to never appear, pretend they don't exist and ask later *)
