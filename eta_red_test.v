Set Printing Universes.
Unset Printing Notations.
Set Printing Implicit.

Variant Tf (T: Type): Type := tf: Tf T.
Check Tf.
(*
Tf
    : Type@{Tf.u0} -> Type@{Tf.u1}
*)
Fail Check Tf = (fun x: Prop => Tf x).
(*
Found type "Prop" where "Type@{Tf.u0}" was expected (universe inconsistency: Cannot enforce Tf.u0 <= Prop).
*)
Check (fun x: Prop => Tf x) = Tf.
(*
@eq (Prop -> Type@{eta_red_test.213}) (fun x : Prop => Tf x) (fun x : Prop => Tf x)
    : Prop
{eta_red_test.213} |= Tf.u1 <= eta_red_test.213
*)
Check @eq (Prop -> Type) Tf (fun x: Prop => Tf x).
(* First fails because inferred type is (Type@{u0} -> Type) *)
Fail Check @eq (Type@{Tf.u0} -> Type) Tf (fun x: Prop => Tf x).
(*
Found type "Prop" where "Type@{Tf.u0}" was expected (universe inconsistency: Cannot enforce Tf.u0 <= Prop).
*)
Check (fun x: Prop => Tf x) = (fun x: Set => Tf x).
(* Yep, truly a wonder of the world, apparently Prop <= Set *)
Fail Check (fun x: Set => Tf x) = (fun x: Prop => Tf x).

Check (fun x => Tf x).
(* NO eta_red_test.240 <= Tf.u0 ???
fun x : Type@{eta_red_test.240} => Tf x
    : Type@{eta_red_test.240} -> Type@{Tf.u1}
{eta_red_test.240} |=
*)
Check (fun x: Type@{Tf.u0+1} => Tf x).
(* WTF
fun x : Type@{Tf.u0+1} => Tf x
    : Type@{Tf.u0+1} -> Type@{Tf.u1}
*)
Check (fun x: Type@{Tf.u1} => Tf x).
(* NO Tf.u1 <= Tf.u0 ???
fun x : Type@{Tf.u1} => Tf x
    : Type@{Tf.u1} -> Type@{Tf.u1}
*)
Check (fun x: Set => Tf x).
(*
fun x : Set => Tf x
    : Set -> Type@{Tf.u1}
*)
Check (fun x: Prop => Tf x).
(*
fun x : Prop => Tf x
    : Prop -> Type@{Tf.u1}
*)


Variant TfT (T: Type): Type := tfT: T -> TfT T.
Check TfT.
(*
TfT
    : Type@{TfT.u0} -> Type@{TfT.u0}
*)
Check (fun x => TfT x).
(* NO eta_red_test.260 <= TfT.u0 ??? return is not TfT.u0 ???
fun x : Type@{eta_red_test.260} => TfT x
    : Type@{eta_red_test.260} -> Type@{eta_red_test.260}
{eta_red_test.260} |=
*)
Check (fun x => TfT x :> Type@{TfT.u0}).
(* return is not TfT.u0 ???
fun x : Type@{eta_red_test.540} => TfT x
    : Type@{eta_red_test.540} -> Type@{eta_red_test.540}
{eta_red_test.540} |= eta_red_test.540 <= TfT.u0
*)
Check (fun x => TfT x) :> Type -> Type@{TfT.u0}.
(* return is not TfT.u0 ???
fun x : Type@{eta_red_test.540} => TfT x
    : Type@{eta_red_test.540} -> Type@{eta_red_test.540}
{eta_red_test.540} |= eta_red_test.540 <= TfT.u0
*)
Check (fun x: Type@{TfT.u0+1} => TfT x).
(* WTF
fun x : Type@{TfT.u0+1} => TfT x
    : Type@{TfT.u0+1} -> Type@{TfT.u0+1}
*)
Check (fun x: Set => TfT x).
(*
fun x : Set => TfT x
    : Set -> Set
*)
Check (fun x: Prop => TfT x).
(*
fun x : Prop => TfT x
    : Prop -> Prop
*)
Fail Check (fun x: Set => TfT x) = (fun x: Type@{TfT.u0} => TfT x).
(* Not able to largen Set?
In environment
x : Type@{TfT.u0}
The term "TfT x" has type "Type@{TfT.u0}" while it is expected to have type "Set" (universe inconsistency: Cannot enforce TfT.u0 <= Set).
*)
Check (fun x: Set => TfT x :> Type@{TfT.u0}) = (fun x: Type@{TfT.u0} => TfT x).
(* Huh?
@eq (Set -> Type@{eta_red_test.797}) (fun x : Set => TfT x) (fun x : Set => TfT x)
     : Prop
{eta_red_test.797} |= TfT.u0 <= eta_red_test.797
*)

Variant TfS (T: Type@{Set+1}): Set := tfS: TfS T.
Check TfS.
(*
TfS
    : Type@{Set+1} -> Set
*)
Check (fun T: Prop => TfS T) = TfS.
Check TfS :> Prop -> Set.
Check TfS :> Set -> Set.
Check TfS :> Type@{Set+1} -> Set.

Print Universes.
