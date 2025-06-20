(*
rlwrap dune exec dev/dune-dbg coqc small_test.v
source db
set break_on_load off
break @Step 830
break @Step 1378

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

(* Context is a meta -1 *)
