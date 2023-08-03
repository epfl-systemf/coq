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
| AtomicAuto   (* automatically pick red based on location *)

type atomic_red_location
val head_let_loc : atomic_red_location
val head_loc     : atomic_red_location

val eval_interface : atomic_red -> Reductionops.e_reduction_function
val apply_atomic   : Environ.env -> atomic_red -> Constr.constr -> Constr.constr
val apply_atomic_at_pos_list  :
  Environ.env -> atomic_red -> Constr.constr -> Constr.atomic_red_location
  -> Evd.evar_map -> Constr.constr option

val apply_at       :
  Constr.constr -> atomic_red_location -> (Constr.constr -> Constr.constr)
  -> Constr.constr option

(* TODO @mbty this should eventually supplant the above functions *)
val apply_atomic_occs :
  Environ.env -> atomic_red -> EConstr.constr
  -> Locus.occurrences Locus.or_like_first -> Evd.evar_map
  -> EConstr.constr option
