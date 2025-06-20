Require Import PrimInt63 PrimArray.

Set Printing Unfolded Projection As Match.

CoInductive Stream :=
  Cons : bool -> Stream -> Stream.
#[projections(primitive)]
CoInductive PStream :=
  PCons { PHead: bool; PTail: PStream }.

Variant Box T := box (x: T).
Record RLB := rlb { rlbI := I }.
Variant VLB := vlb: let vlbI := I in VLB.

Axiom epsilonvlb: VLB.

#[projections(primitive)]
Record Wrap := wrap { unwrap: True }.
#[projections(primitive)]
Record BPair := bpair { pfst: bool; psnd: bool }.
#[projections(primitive)]
Record BPair2 := bpair2 { pfst2: bool; psnd2: bool }.
#[projections(primitive)]
Record PBox T := pbox { punbox: T }.

Axiom f: nat -> nat.

Axiom epsilonb: bool.
Axiom epsilonpbn: PBox True.
Axiom epsilonbp: BPair.
Axiom epsilonbp': BPair.

Variant VLBs :=
| vlbf: let vlbfI := I in let vlbfF := (fun x: True => x) in VLBs
| vlbt: let vlbtI := I in let vlbtF := (fun x: True => x) in VLBs
.

Definition altTrue := True.
Axiom epsilonvlbs: VLBs.
Axiom epsilonbat: Box altTrue.
Axiom epsilonbt: Box True.

Variant VLBP (T: Type) := vlbp: let vlbpT := T in VLBP T.
Axiom epsilonvlbpt: VLBP True.

Variant TfT (T: Type): Type := tfT.
Variant TfS (T: Type): Set := tfS.

#[projections(primitive)]
Inductive RA := A {
    ttfst: bool;
    ttsnd: bool
  }
with RB := B {
    tttrd: bool;
    ttfth: bool
  }
with RC := C {
    ttfif: bool
  }
.
Axiom epsilonra: RA.
Axiom epsilonrb: RB.
Axiom epsilonrc: RC.

Inductive vec : nat -> Set :=
| evec : vec 0
| bvec n : bool -> vec n -> vec (S n)
.
Axiom epsilonvec: vec 1.
Definition altS k := S k.
Notation NVLBP := (VLBP nat).
Notation "'nvlbp'" := (VLBP).

(* Cast reduction *)
Eval step cast in (id O): nat.
Eval step head in (id O): nat.
Eval step cbv in O: nat.
(* Beta app reduction *)
Eval step beta in (fun x => x) (id O).
Eval step head in (fun x => x) (id O).
Eval step cbv in (fun x => x) O.
Eval step beta in (fun f => f) (@id nat) (id O).
Eval step head in (fun f => f) (@id nat) (id O).
Eval step cbv in (fun f => f) (fun x => x) (id O).
Eval step beta in (fun f => f (@id nat)) (id (@id (nat -> nat))) O.
Eval step head in (fun f => f (@id nat)) (id (@id (nat -> nat))) O.
Eval step cbv in (fun f => f (fun x => x)) (fun x => x) (id O).
Fail Eval step head in id O.
(* Zeta reduction *)
Eval step zeta in let x := id O in x.
Eval step head in let x := id O in x.
Eval step cbv in let x := O in x.
(* Zeta_match x reduction *)
Eval step zeta_match "nvlbp" 1 1 in match id (vlbp nat) with vlbp _ x => id x end.
Eval step zeta_match NVLBP 1 1 in match id (vlbp nat) with vlbp _ x => id x end.
Eval step zeta_match VLBP 1 1 in match id (vlbp nat) with vlbp _ x => id x end.
Eval step zeta_match vlbp in match id (vlbp nat) with vlbp _ x => id x end.
Eval step zeta_match VLBP in match id (vlbp nat) with vlbp _ x => id x end.
Eval step zeta_match vlb 1 in match id vlb with vlb x => id x end.
Eval step head in match id vlb with vlb x => id x end.
Eval step cbv in match epsilonvlb with vlb x => id x end.
Eval step zeta_match vlbp 1 in match id (vlbp True) with vlbp _ x => id x end.
Eval step head in match id (vlbp True) with vlbp _ x => id x end.
Eval step cbv in match epsilonvlbpt with vlbp _ x => id x end.
Eval step zeta_match vlbt 1 in match id vlbt with vlbf x f => id f (id x) | vlbt x f => id f (id x)  end.
Eval step zeta_match vlbf 1 in match id vlbt with vlbf x f => id f (id x) | vlbt x f => id f (id x) end.
Eval step zeta_match vlbt 2 in match id vlbt with vlbf x f => id f (id x) | vlbt x f => id f (id x) end.
Eval step zeta_match vlbf 2 in match id vlbt with vlbf x f => id f (id x) | vlbt x f => id f (id x) end.
Eval step head in match id vlbt with vlbf x f => id f (id x) | vlbt x f => id f (id x) end.
Eval step head in match id vlbt with vlbf x f => id x | vlbt x f => id f (id x) end.
Eval step head in match id vlbt with vlbf x f => I | vlbt x f => id f (id x) end.
Eval step head in match id vlbt with vlbf x f => I | vlbt x f => id x end.
Eval step cbv in match epsilonvlbs with vlbf x f => id f (id x) | vlbt x f => id f (id x) end.
Eval step cbv in match epsilonvlbs with vlbf x f => id x | vlbt x f => id f (id x) end.
Eval step cbv in match epsilonvlbs with vlbf x f => I | vlbt x f => id f (id x) end.
Eval step cbv in match epsilonvlbs with vlbf x f => I | vlbt x f => id x end.
Fail Eval step zeta_match vlbI in match id vlb with vlb x => id x end.
Fail Eval step zeta_match vlb 2 in O.
Fail Eval step head in match id epsilonvlb with vlb x => I end.
Fail Eval step cbv in match epsilonvlb with vlb x => I end.
(* Delta reduction *)
Eval step delta in Nat.add.
Eval step head in Nat.add.
Eval step cbv in Nat.add.
Eval step delta in (wrap (id I)).(unwrap).
Eval step head in (wrap (id I)).(unwrap).
Eval step cbv in (wrap I).(unwrap).
Eval step delta in (add 0 0)%uint63.
Eval step head in (add 0 0)%uint63.
Eval step cbv in (add 0 0)%uint63.
Fail Eval step delta in (add 0)%uint63.
Fail Eval step head in (add 0)%uint63.
Fail Eval step cbv in (add 0)%uint63.
Fail Eval step delta in (add (id 0) 0)%uint63.
Fail Eval step head in (add (id 0) 0)%uint63.
Fail Eval step delta in epsilonb.
Fail Eval step head in epsilonb.
Fail Eval step cbv in epsilonb.
Section toto.
  Variable z: nat.
  Fail Eval step delta in z.
  Fail Eval step head in z.
  Fail Eval step cbv in z.
End toto.
Goal True.
    pose (e := True).
    assert e.
    step delta. Undo.
    step head. Undo.
    step cbv.
Abort.
(* Eta expansion/reduction *)
Set Printing Universes.
Check ltac:(let tm := eval step eta in PBox in exact tm).
Check ltac:(let tm := eval step eta in TfT in exact tm).
Check ltac:(let tm := eval step eta in TfS in exact tm).
Check ltac:(let tm := eval step eta' in (fun T: Type@{PBox.u0} => PBox T) in exact tm).
Check ltac:(let tm := eval step eta' in (fun T: Type@{TfT.u0} => TfT T) in exact tm).
Check ltac:(let tm := eval step eta' in (fun T: Type@{TfS.u0} => TfS T) in exact tm).
Check ltac:(let tm := eval step head in (fun T: Type@{PBox.u0} => PBox T) in exact tm).
Check ltac:(let tm := eval step head in (fun T: Type@{TfT.u0} => TfT T) in exact tm).
Check ltac:(let tm := eval step head in (fun T: Type@{TfS.u0} => TfS T) in exact tm).
Check ltac:(let tm := eval step cbv in (fun T: Type@{PBox.u0} => PBox T) in exact tm).
Check ltac:(let tm := eval step cbv in (fun T: Type@{TfT.u0} => TfT T) in exact tm).
Check ltac:(let tm := eval step cbv in (fun T: Type@{TfS.u0} => TfS T) in exact tm).
Fail Eval step eta' in (fun T => PBox T).
Fail Eval step eta' in (fun T => TfT T).
Fail Eval step eta' in (fun T => TfS T).
Fail Eval step head in (fun T => PBox T).
Fail Eval step head in (fun T => TfT T).
Fail Eval step head in (fun T => TfS T).
Fail Eval step cbv in (fun T => PBox T).
Fail Eval step cbv in (fun T => TfT T).
Fail Eval step cbv in (fun T => TfS T).
Fail Eval step eta' in (fun T: Set => PBox T).
Fail Eval step eta' in (fun T: Set => TfT T).
Fail Eval step eta' in (fun T: Set => TfS T).
Fail Eval step eta' in fun T: Prop => PBox T.
Fail Eval step head in fun T: Prop => PBox T.
Fail Eval step cbv in fun T: Prop => PBox T.
Fail Eval step eta' in fun x => pair x O.
Fail Eval step head in fun x => pair x O.
Fail Eval step cbv in fun x => pair x O.
Unset Printing Universes.
Eval step eta' in pbox True (id epsilonpbn).(punbox _).
Eval step head in pbox True (id epsilonpbn).(punbox _).
Eval step cbv in pbox True match epsilonpbn with {| punbox := x |} => x end.
Eval step eta' in bpair (id epsilonbp).(pfst) (id epsilonbp).(psnd).
Eval step head in bpair (id epsilonbp).(pfst) (id epsilonbp).(psnd).
Eval step cbv in bpair match epsilonbp with {| pfst := x |} => x end match epsilonbp with {| psnd := x |} => x end.
Eval step eta' in A epsilonra.(ttfst) epsilonra.(ttsnd).
Eval step head in A epsilonra.(ttfst) epsilonra.(ttsnd).
Eval step cbv in A match epsilonra with {| ttfst := x |} => x end match epsilonra with {| ttsnd := x |} => x end.
Eval step eta' in B epsilonrb.(tttrd) epsilonrb.(ttfth).
Eval step head in B epsilonrb.(tttrd) epsilonrb.(ttfth).
Eval step cbv in B match epsilonrb with {| tttrd := x |} => x end match epsilonrb with {| ttfth := x |} => x end.
Eval step eta' in C epsilonrc.(ttfif).
Eval step head in C epsilonrc.(ttfif).
Eval step cbv in C match epsilonrc with {| ttfif := x |} => x end.
Fail Eval step eta' in bpair (id epsilonbp).(pfst).
Fail Eval step head in bpair (id epsilonbp).(pfst).
Fail Eval step cbv in bpair match epsilonbp with {| pfst := x |} => x end.
Fail Eval step eta' in wrap (id epsilonpbn).(punbox _).
Fail Eval step head in wrap (id epsilonpbn).(punbox _).
Fail Eval step cbv in wrap match epsilonpbn with {| punbox := x |} => x end.
Fail Eval step eta' in bpair (id epsilonbp).(psnd) (id epsilonbp).(pfst).
Fail Eval step head in bpair (id epsilonbp).(psnd) (id epsilonbp).(pfst).
Fail Eval step cbv in bpair match epsilonbp with {| psnd := x |} => x end match epsilonbp with {| pfst := x |} => x end.
Fail Eval step eta' in bpair2 (id epsilonbp).(pfst) (id epsilonbp).(psnd).
Fail Eval step head in bpair2 (id epsilonbp).(pfst) (id epsilonbp).(psnd).
Fail Eval step cbv in bpair2 match epsilonbp with {| pfst := x |} => x end match epsilonbp with {| psnd := x |} => x end.
Fail Eval step eta' in bpair (id epsilonbp).(pfst) (epsilonbp).(psnd).
Fail Eval step head in bpair (id epsilonbp).(pfst) (epsilonbp).(psnd).
Fail Eval step cbv in bpair match epsilonbp with {| pfst := x |} => x end match epsilonbp' with {| psnd := x |} => x end.
Fail Eval step eta' in A epsilonrb.(tttrd) epsilonrb.(ttfth).
Fail Eval step head in A epsilonrb.(tttrd) epsilonrb.(ttfth).
Fail Eval step cbv in A match epsilonrb with {| tttrd := x |} => x end match epsilonrb with {| ttfth := x |} => x end.
Fail Eval step eta' in B epsilonra.(ttfst) epsilonra.(ttsnd).
Fail Eval step head in B epsilonra.(ttfst) epsilonra.(ttsnd).
Fail Eval step cbv in B match epsilonra with {| ttfst := x |} => x end match epsilonra with {| ttsnd := x |} => x end.
Fail Eval step eta' in C epsilonra.(ttfst).
Fail Eval step head in C epsilonra.(ttfst).
Fail Eval step cbv in C match epsilonra with {| ttfst := x |} => x end.
(* Evar reduction *)
Goal True.
  refine (_ _).
  exact (@id True).
  step evar. Undo.
  step head. Undo.
  step cbv.
  cbv.
  Fail step head.
  Fail step cbv.
Abort.
(* Fix reduction *)
Eval step fix in (fix any (x: bool) := x) false.
Eval step head in (fix any (x: bool) := x) false.
Eval step cbv in (fix any (x: bool) := x) false.
Eval step fix in (fix any T (x: bool) := x) (id bool) false.
Eval step head in (fix any T (x: bool) := x) (id bool) false.
Eval step cbv in (fix any T (x: bool) := x) bool false.
Eval step fix in (fix is_even x := match x with O => true | S n => is_odd n end with is_odd n := match n with O => false | S n => is_even n end for is_even) O.
Eval step head in (fix is_even x := match x with O => true | S n => is_odd n end with is_odd n := match n with O => false | S n => is_even n end for is_even) O.
Eval step cbv in (fix is_even x := match x with O => true | S n => is_odd n end with is_odd n := match n with O => false | S n => is_even n end for is_even) O.
Fail Eval step fix in (fix any (x: bool) := x) (id false).
Fail Eval step head in (fix any (x: bool) := x) (id false).
Fail Eval step cbv in (fix any (x: bool) := x) epsilonb.
Fail Eval step fix in (fix any T (x: bool) := x) (id bool).
Fail Eval step head in (fix any T (x: bool) := x) (id bool).
Fail Eval step cbv in (fix any T (x: bool) := x) bool.
(* Fix' reduction *)
Eval step fix' in (fix any (x: bool) := x).
Eval step fix' in (fix is_even x := match x with O => true | S n => is_odd n end with is_odd n := match n with O => false | S n => is_even n end for is_even).
(* Cofix reduction *)
Eval step cofix in match (cofix x := Cons true x) with Cons h t => h end.
Eval step head in match (cofix x := Cons true x) with Cons h t => h end.
Eval step cbv in match (cofix x := Cons true x) with Cons h t => h end.
Eval step cofix in (cofix x := PCons true x).(PHead).
Eval step head in match (cofix x := PCons true x) with {| PHead := x |} => x end.
Eval step cbv in match (cofix x := PCons true x) with {| PHead := x |} => x end.
Eval step cofix in match cofix x := Cons true y with y := Cons false x for x with Cons h t => t end.
Eval step head in match cofix x := Cons true y with y := Cons false x for x with Cons h t => t end.
Eval step cbv in match cofix x := Cons true y with y := Cons false x for x with Cons h t => t end.
Eval step cofix in (cofix x := PCons true y with y := PCons false x for x).(PTail).
Eval step head in match cofix x := PCons true y with y := PCons false x for x with {| PTail := x |} => x end.
Eval step cbv in match cofix x := PCons true y with y := PCons false x for x with {| PTail := x |} => x end.
Fail Eval step head in cofix x := PCons true y with y := PCons false x for x.
Fail Eval step cbv in cofix x := PCons true y with y := PCons false x for x.
(* Cofix' reduction *)
Eval step cofix' in cofix x := Cons true x.
Eval step cofix' in cofix x := Cons true y with y := Cons false x for x.
(* Match reduction *)
Eval step match in match I with I => id O end.
Eval step head in match I with I => id O end.
Eval step cbv in match I with I => id O end.
Eval step match in match true with true => id false | false => id true end.
Eval step head in match true with true => id false | false => id true end.
Eval step cbv in match true with true => id false | false => id true end.
Eval step match in match false with true => id false | false => id true end.
Eval step head in match false with true => id false | false => id true end.
Eval step cbv in match false with true => id false | false => id true end.
Eval step match in match box nat (id O) with box _ x => id x end.
Eval step head in match box nat (id O) with box _ x => id x end.
Eval step cbv in match box nat O with box _ x => id x end.
Eval step match in match box (nat -> nat) (id S) with box _ f => id f (id O) end.
Eval step head in match box (nat -> nat) (id S) with box _ f => id f (id O) end.
Eval step cbv in match box (nat -> nat) S with box _ f => id f (id O) end.
Eval step match in match rlb with rlb x => id x end.
Eval step head in match rlb with rlb x => id x end.
Eval step cbv in match rlb with rlb x => id x end.
Eval step match in match vlb with vlb x => id x end.
Eval step head in match vlb with vlb x => id x end.
Eval step cbv in match vlb with vlb x => id x end.
Fail Eval step head in match epsilonvlb with vlb => id I end.
Fail Eval step cbv in match epsilonvlb with vlb => I end.
Fail Eval step head in match id vlb with vlb => id I end.
(* Projection reduction *)
Eval step match in match wrap (id I) with {| unwrap := x |} => x end.
Eval step head in match wrap (id I) with {| unwrap := x |} => x end.
Eval step cbv in match wrap I with {| unwrap := x |} => x end.
Eval step match in match bpair (id true) (id false) with {| pfst := x |} => x end.
Eval step head in match bpair (id true) (id false) with {| pfst := x |} => x end.
Eval step cbv in match bpair true false with {| pfst := x |} => x end.
Eval step match in match bpair (id true) (id false) with {| psnd := x |} => x end.
Eval step head in match bpair (id true) (id false) with {| psnd := x |} => x end.
Eval step cbv in match bpair true false with {| psnd := x |} => x end.
Eval step match in match pbox (id nat) (id O) with {| punbox := x |} => x end.
Eval step head in match pbox (id nat) (id O) with {| punbox := x |} => x end.
Eval step cbv in match pbox nat O with {| punbox := x |} => x end.

(* Reduce head under App *)
Eval step cbv in match I with I => @id nat end (id O).
Eval step cbv in match I with I => Nat.add end (id O) (id O).
(* Reduce first arg under App *)
Eval step cbv in (fun x => I) ((fun x => x) O).
Eval step cbv in (fun f x => f x) ((fun x => x) S) (id O).
(* Reduce under Cast *)
Eval step cbv in Nat.add : nat -> nat -> nat.
(* Reduce substituend under LetIn *)
Eval step cbv in let x := Nat.add in id O.
(* Reduce elements under Array *)
Eval step cbv in [| id O ; id O | (fun x => x) O :> id nat |].
Eval step cbv in [| (fun x => x) O ; id O | O :> id nat |].
Eval step cbv in [| O ; (fun x => x) O | O :> id nat |].
(* Reduce type under Array *)
Eval step cbv in [| O ; O | O :> id nat |].
(* Reduce type under Lambda *)
Eval step cbv in fun x: (fun x => x) nat => x.
(* Reduce body under Lambda *)
Eval step cbv in fun x: id Set => (fun x: Set => x) x.
(* Reduce matchee under Case *)
Eval step cbv in match (fun x => x) I with I => O end.
(* Reduce branches under Case *)
Eval step cbv in match epsilonb with true => (fun x => x) O | false => id O end.
Eval step cbv in match epsilonb with true => O | false => (fun x => x) O end.
Eval step cbv in match epsilonbt with box _ x => (fun (f: True -> nat -> nat) y => f x y) end.
(* Reduce parameter under case *)
Eval step cbv in match epsilonbat with box _ _ => O end.
(* Reduce return type under case *)
Goal (fun _ => eq_refl) =
  match epsilonvec as value in vec (S natural as ii) return forall _: (exists z, value = bvec natural true z), S natural = (altS natural) with
  | bvec n _ _ => fun _ => eq_refl (S n)
  | evec => fun f: False => match f return S O = S O with end
  end.
  step cbv.
  step cbv.
Abort.
(* Reduce body under Fix *)
Eval step cbv in fix is_even n := (fun x => x) match n with O => true | S n => is_odd n end with is_odd n := id match n with O => false | S n => is_even n end for is_even.
Eval step cbv in fix is_even n := match n with O => true | S n => is_odd n end with is_odd n := (fun x => x) match n with O => false | S n => is_even n end for is_even.
(* Reduce type under Fix *)
Eval step cbv in fix length l : (fun x => x) nat := match l with cons h t => S (length t) | nil => 0 end.
(* Reduce body under CoFix *)
Eval step cbv in cofix x := (fun x => x) (Cons true y) with y := id (Cons false x) for x.
Eval step cbv in cofix x := Cons true y with y := (fun x => x) (Cons false x) for x.
(* Reduce type under CoFix *)
Eval step cbv in cofix x : (fun x => x) Stream := Cons true x.
(* Reduce in Evar context *)
Goal True.
  unshelve refine ((fun x y => _) _ _).
  3: exact ((fun x => x) I).
  3: step cbv. (* Reduce evar in evar context *)
  3: step cbv.
Abort.
(* Reduce sort under Prod *)
Eval step cbv in forall x: (fun x => x) True, id True.
(* Reduce type under Prod *)
Eval step cbv in forall x: True, (fun x => x) True.

(* UIP reduction *)
Set Definitional UIP.
Variant Seq [T] (x: T): T -> SProp := seq: Seq x x.
Variant SUnit: SProp := sunit: SUnit.
Axiom epsilonsnn: Seq nat nat.
Axiom epsilon01: Seq 0 1.
Axiom epsilonsu: SUnit.

Eval step uip in match (fun x => x) epsilonsu with sunit => id O end.
Eval step head in match (fun x => x) epsilonsu with sunit => id O end.
Eval step cbv in match epsilonsu with sunit => id O end.
Eval step uip in match (fun x => x) epsilonsnn with seq _ => id O end.
Eval step head in match (fun x => x) epsilonsnn with seq _ => id O end.
Eval step cbv in match epsilonsnn with seq _ => id O end.
Fail Eval step uip in match epsilon01 return nat with seq _ => id O end.
Fail Eval step head in match epsilon01 return nat with seq _ => id O end.
Fail Eval step cbv in match epsilon01 return nat with seq _ => O end.
