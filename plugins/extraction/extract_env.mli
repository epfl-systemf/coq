(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s This module declares the extraction commands. *)

open Names
open Libnames

val simple_extraction : opaque_access:Global.indirect_accessor -> qualid -> unit
val full_extraction : opaque_access:Global.indirect_accessor -> string option -> qualid list -> unit
val separate_extraction : opaque_access:Global.indirect_accessor -> qualid list -> unit
val extraction_library : opaque_access:Global.indirect_accessor -> bool -> lident -> unit

(* For the test-suite : extraction to a temporary file + ocamlc on it *)

val extract_and_compile : opaque_access:Global.indirect_accessor -> qualid list -> unit

(* For debug / external output via coqtop.byte + Drop : *)

val mono_environment :
 Table.t -> opaque_access:Global.indirect_accessor -> GlobRef.t list -> ModPath.t list -> Miniml.ml_structure

(* Used by the Relation Extraction plugin *)

val print_one_decl :
  Table.t -> Miniml.ml_structure -> ModPath.t -> Miniml.ml_decl -> Pp.t

(* Used by Extraction Compute *)

val structure_for_compute :
  opaque_access:Global.indirect_accessor -> Environ.env -> Evd.evar_map -> EConstr.t ->
    Table.t * Miniml.ml_decl list * Miniml.ml_ast * Miniml.ml_type

(* Show the extraction of the current ongoing proof *)

val show_extraction : pstate:Declare.Proof.t -> unit
