(*
rlwrap dune exec dev/dune-dbg coqc small_test.v
source db
set break_on_load off
break @Conversion 999

*)

(* to break on a module:
break @Library 385
r
*)

(*
  simple_progress (syntactic progress)
  simple_repeat (syntactic progress)
  (* motivating example *)
  "Debug mode" with ability to focus on a subterm, cannot be done with fun (let in)
  ^ submit this idea to Clément
*)

Goal (fun a => 2 + (a + a)) 8 = 18.
Proof.
  Notation cbvt tm :=
    (ltac:(let tm' := (eval cbv in tm) in
           exact tm')).

  Fail change (?x + ?x) with (cbvt (x + x)). (* DOES NOT WORK UNDER BINDER *)
  compute at 2.
  unfold Nat.add at 2.
  fold Nat.add at 2.
  simpl Nat.add at 2.
  pattern Nat.add at 2.
  vm_compute Nat.add at 2.
Abort.

(* cbv1. *)
(* cbv1 (?x + ?x). *)

(* Context is a meta -1 *)

Goal forall a, a + (2 + 2) = 18.
Proof.
  match goal with
  | [ |- context C[?x + ?x as tm]] =>
      (* DOES NOW WORK UNDER BINDER *)
      idtac C;
      let tm' := (eval cbv in tm) in
      (idtac tm';
      let C' := context C [tm'] in
      change C')
  end.
Abort.
