(* @mbty I wanted to call this file atomic but this leads to conflict with the
   name of the kernel-side implementation. *)

(** Parameter of the atomic tactic. Produced during parsing (see
    plugins/ltac/g_tactic.mlg). Unrelated to red_atom. *)
type atomic_red =
| AtomicFun    (* function   application | beta  reduction *)
| AtomicFix    (* fixpoint   expansion   | fix   reduction *)
| AtomicCoFix  (* cofixpoint expansion   | cofix reduction *)
| AtomicMatch  (* match      reduction   | match reduction *)
| AtomicLet    (* let-in     reduction   | zeta  reduction *)
| AtomicUnfold (* definition expansion   | delta reduction *)

type atomic_red_location
val default_location : atomic_red_location

val eval_interface : atomic_red -> Reductionops.e_reduction_function
val apply_atomic :
  Environ.env -> atomic_red -> Constr.constr -> Constr.constr
val apply_at :
  Constr.constr -> atomic_red_location -> (Constr.constr -> Constr.constr)
  -> Constr.constr option

(* TODO rm *)
val atomic_let_wrapped : Constr.constr -> Constr.constr

val apply_atomic_occs :
  Environ.env -> atomic_red -> EConstr.constr
  -> Locus.occurrences Locus.or_like_first -> Evd.evar_map
  -> EConstr.constr option
