(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* TODO document *)

val atomic_cofix   : unit Proofview.tactic
val atomic_fix   : unit Proofview.tactic
val atomic_fun   : unit Proofview.tactic
val atomic_unfold: unit Proofview.tactic
val atomic_let   : unit Proofview.tactic
val atomic_match : unit Proofview.tactic

val atomic_let_rev: unit Proofview.tactic
