(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ

val apply_hints   : env -> constr -> atomic_red_location list -> constr
val reduce_at_pos : env -> constr -> atomic_red_location      -> constr
(* TODO @mbty remove following *)
val print_at      : constr -> atomic_red_location -> string
val focus         : constr -> atomic_red_location -> constr option
