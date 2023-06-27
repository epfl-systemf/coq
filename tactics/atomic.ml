(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* A collection of atomic reductions:
   - atomic_cofix  ("atomic cofix") : expands a cofixpoint
   - atomic_fix    ("atomic fix")   : turn an anonymous fixpoint into a lambda
   - atomic_fun    ("atomic fun")   : pass an argument to an anonymous function
   - atomic_unfold ("atomic unfold"): replace a global constant with its
     definition
   - atomic_let    ("atomic let")   : invert a let binding
   - atomic_match  ("atomic match") : evaluate a match

  See plugins/ltac/g_atomic.ml* for the definition of the tactics. *)

(* For the time being, the reductions apply to X in let abc = X in Y. They are
   meant to be used after the expression has been transformed to this form, with
   the part that should be reduced being located at position X ("set" and
   "revert" come in handy for this purpose). *)

(* TODO error messages *)
(* TODO zipper *)
(* TODO kernel side implementation *)
(* TODO the computations should occur in the same way as in the kernel. Why
   not reuse the functions defined in there? *)
(* TODO avoid checks (see TacChange (false, ...)); not compatible with
   Tactics.change_concl, though. *)
(* TODO apply appropriate step based on position (there can never be more than
   one simplification applying to a given position anyways) *)

(* open Constr *)

(* let test : EConstr.t = Rel 1 *)
(*   (1* match c with *1) *)
(*   (1* | Rel _ -> Rel 1 *1) *)
(*   (1* | _ -> Rel 1 *1) *)

let atomic_no_env f =
  Proofview.Goal.enter
    (fun gl ->
      let constr = EConstr.Unsafe.to_constr (Proofview.Goal.concl gl) in
      Tactics.change_concl (EConstr.of_constr (f constr))
    )

(* TODO Can't access constr's internals without exposing the type? *)

(* Fixpoint unfolding *)
let atomic_cofix_aux term =
  match Constr.kind term with
  | CoFix ((id, ((binders, types, bodies) as fb))) ->
    let body  = bodies.(id) in
    let fixes =
      List.init
        (Array.length bodies)
        (fun id -> Constr.of_kind (CoFix (id, fb)))
    in
    Vars.substl fixes body
  | _ -> term

(* Fixpoint unfolding *)
(* TODO should rather make use of substnl, right? *)
(* FIXME temporary: can be applied to smthg of the form App (fix, args) for
   convenience (limits of set when reducing in head let ); remove eventually *)
let atomic_fix_aux term =
  match Constr.kind term with
  | Fix ((decreasing_arguments, id), ((binders, types, bodies) as fb)) ->
    let body  = bodies.(id) in
    let fixes =
      List.init
        (Array.length bodies)
        (fun id -> Constr.of_kind (Fix ((decreasing_arguments, id), fb)))
    in
    Vars.substl fixes body
  | App (what, args) ->
   (match (Constr.kind what) with
    | Fix ((decreasing_arguments, id), ((binders, types, bodies) as fb)) ->
      let body  = bodies.(id) in
      let fixes =
        List.init
          (Array.length bodies)
          (fun id -> Constr.of_kind (Fix ((decreasing_arguments, id), fb)))
      in
      Constr.of_kind (App (Vars.substl fixes body, args))
    | _ -> term)
  | _ -> term

(* Lambda application *)
let atomic_fun_aux term =
  match Constr.kind term with
  | App (what, args) ->
    (match (Constr.kind what) with
    | Lambda (lname, lype, lbody) ->
      (match Array.to_list args with
      | []    -> term
      | h::[] -> Vars.subst1 h lbody
      | h::t  -> Constr.of_kind (App ((Vars.subst1 h lbody), Array.of_list t)))
    | _ -> term)
  | _ -> term

(* Definition unfolding *)
let atomic_unfold_aux env term =
  match Constr.kind term with
  | Const (constant_info, universe_info) ->
    let pbody = (Environ.lookup_constant constant_info env).const_body in
    (match pbody with
    | Def v -> v
    | _ -> term (* TODO What about other constructors? *)
    )
  | _ -> term

(* Let unfolding *)
let atomic_let_aux term =
  match Constr.kind term with
  | LetIn (name_info, value, value_type, body) ->
    (match name_info.binder_name with
    | Name (id) -> Vars.(subst1 value (subst_var id body))
    | _ -> term)
  | _ -> term

(* Match application *)
(* TODO substnl offset? *)
let atomic_match_aux term =
  match Constr.kind term with
  | Case (
      case_info, universe_info, parameters, return_type, inversion_info, what,
      branches_info
    ) ->
    (match Constr.kind what with
     | Construct ((type_info, constructor_id), construct_universe_info) ->
       (* Constructors indices start at 1 for some reason *)
       snd branches_info.(constructor_id - 1)
     | App (what, args) ->
       (match Constr.kind what with
        | Construct ((type_info, constructor_id), construct_universe_info) ->
          let (branch_args, branch_body) = branches_info.(constructor_id - 1) in
          let vars =
            List.combine (Array.to_list branch_args) (Array.to_list args)
          in
          (match List.length vars with
          | 0 -> Constr.of_kind (Rel 1)
          | _ -> Vars.substl (List.rev (Array.to_list args)) branch_body
          )
        | _ -> term
       )
     | _ -> term
    )
  | _ -> term

type atomic_red =
| CoFixUnfold
| FixUnfold
| FunApply
| DefUnfold
| LetUnfold
| MatchApply

(* TODO ensure that every constr/types occurrence in Constr is covered *)
(* TODO do manual type changes even make sense? I guess so but an actual example
   of why would be nice *)
type atomic_red_direction =
| EvarItem of int
| CastFrom
| CastTo
| LambdaBody
| LambdaArgType
| LetInDef
| LetInType
| LetInBody
| AppBody
| AppArg of int
| CaseBranch of int
| CaseParam of int
| CaseExpr
| CaseReturnType
| FixBody
| FixBodyMut of int
| FixType
| FixTypeMut
| CoFixBody
| CoFixBodyMut of int
| CoFixType
| CoFixTypeMut of int
| ProjRecord
| ArrayNth of int
| ArrayDefaultVal
type atomic_red_location = atomic_red_direction list

let rec apply_to_nth_option_aux f l n =
  match l with
  | h::t ->
    if (n == 0)
    then Some ((f h)::t)
    else
      let res = (apply_to_nth_option_aux f t (n - 1)) in
      Option.map (fun res -> h::res) res
  | _ -> None
let rec apply_to_nth_option f l n =
  if (n < 0) then None else apply_to_nth_option_aux f l n

(* let rec apply_at term pos f : term option = *)
(*   match pos, term with *)
(*   | nil -> Some (f term) *)
(*   | (EvarItem (n))::t, Evar (evar_info, context) -> *)
(*     if SList.length context >= n then *)
(*   | CastFrom::t, Cast (obj, cast_kind, to_type) -> *)
(*     let res = apply_at obj t f in *)
(*     Option.map (fun res -> Cast (res, cast_kind, to_type)) res *)
(*   | CastTo::t, Cast (obj, cast_kind, to_type) -> *)
(*     let res = apply_at to_type t f in *)
(*     Option.map (fun res -> Cast (obj, cast_kind, res)) res *)
(*   | LambdaBody::t, Lambda (name_info, arg, body) -> *)
(*     let res = apply_at body t f in *)
(*     Option.map (fun res -> Lambda (name_info, arg, res)) res *)
(*   | LambdaArgType::t, Lambda (name_info, arg, body) -> *)
(*     let res = apply_at arg t f in *)
(*     Option.map (fun res -> Lambda (name_info, res, body)) res *)
(*   | LetInDef::t, LetIn (name_info, value, value_type, body) -> *)
(*     let res = apply_at value t f in *)
(*     Option.map (fun res -> LetIn (name_info, res, value_type, body)) res *)
(*   | LetInType::t, LetIn (name_info, value, value_type, body) -> *)
(*     let res = apply_at value_type t f in *)
(*     Option.map (fun res -> LetIn (name_info, value, res, body)) res *)
(*   | LetInBody::t, LetIn (name_info, value, value_type, body) -> *)
(*     let res = apply_at body t f in *)
(*     Option.map (fun res -> LetIn (name_info, value, value_type, res)) res *)
(*   | AppBody::t, App (obj, to_args) -> *)
(*     let res = apply_at obj t f in *)
(*     Option.map (fun res -> App (res, to_args)) res *)
(*   | (AppArg (n))::t, App (obj, to_args) -> *)
(*     let res = apply_to_nth_option n obj args in *)
(*     Option.map (fun res -> App (obj, res)) res *)
(*   | (CaseBranch (n))::t, *)
(*     Case ( *)
(*       case_info, universe_info, parameters, return_type, inversion_info, *)
(*       matched_term, branches_info *)
(*     ) -> *)
(*     (1* TODO specialize for branches_info *1) *)
(*     let res = apply_to_nth_option n branches_info args in *)
(*     Option.map *)
(*       (fun res -> *)
(*         Case ( *)
(*           case_info, universe_info, parameters, return_type, inversion_info, *)
(*           matched_term, res *)
(*         ) *)
(*       ) *)
(*       res *)
(*   | (CaseParam (n))::t, *)
(*     Case ( *)
(*       case_info, universe_info, parameters, return_type, inversion_info, *)
(*       matched_term, branches_info *)
(*     ) -> *)
(*     let res = apply_to_nth_option n parameters f in *)
(*     Option.map *)
(*       (fun res -> *)
(*         Case ( *)
(*           case_info, universe_info, res, return_type, inversion_info, *)
(*           matched_term, branches_info *)
(*         ) *)
(*       ) *)
(*       res *)
(*   | CaseExpr::t, *)
(*     Case ( *)
(*       case_info, universe_info, parameters, return_type, inversion_info, *)
(*       matched_term, branches_info *)
(*     ) -> *)
(*     let res = apply_at matched_term t f in *)
(*     Option.map *)
(*       (fun res -> *)
(*         Case ( *)
(*           case_info, universe_info, parameters, return_type, inversion_info, *)
(*           res, branches_info *)
(*         ) *)
(*       ) *)
(*       res *)
(*   | CaseReturnType::t, *)
(*     Case ( *)
(*       case_info, universe_info, parameters, return_type, inversion_info, *)
(*       matched_term, branches_info *)
(*     ) -> *)
(*     let res = apply_at return_type t f in *)
(*     Option.map *)
(*       (fun res -> *)
(*         Case ( *)
(*           case_info, universe_info, parameters, eturn_type, inversion_info, *)
(*           res, branches_info *)
(*         ) *)
(*       ) *)
(*       res *)
(*   | FixBody::t, Fix ((refs, (names, types, constrs))) -> *)
(*     let res = apply_to_nth_option 0 parameters f in *)
(*     Option.map (fun res -> Fix ((refs, (names, types, res)))) res *)
(*   | (FixBodyMut (n))::t *)
(*   | FixType::t -> *)
(*     let res = apply_to_nth_option 0 parameters f in *)
(*     Option.map (fun res -> Fix ((refs, (names, types, res)))) res *)
(*   | (FixTypeMut (n))::t *)
(*   | CoFixBody::t *)
(*   | (CoFixBodyMut (n))::t *)
(*   | CoFixType::t, CoFix (()) *)
(*     let res = apply_at record_obj t f in *)
(*     Option.map (fun res -> ProjRecord (projection_info, res)) res *)
(*   | (CoFixTypeMut (n))::t *)
(*   | ProjRecord::t, Proj (projection_info, record_obj) -> *)
(*     let res = apply_at record_obj t f in *)
(*     Option.map (fun res -> ProjRecord (projection_info, res)) res *)

(* TODO full implementation, see above *)
let rec apply_at (term: Constr.constr) pos (f: Constr.constr -> Constr.constr) =
  match pos, Constr.kind term with
  | LetInDef::t, LetIn (name_info, value, value_type, body) ->
    let res = apply_at value t f in
    Option.map
      (fun res -> Constr.of_kind (LetIn (name_info, res, value_type, body)))
      res
  | [], e -> Some (f (Constr.of_kind e))
  | _, _  -> None

let apply_atomic env red term =
  match red with
  | CoFixUnfold -> atomic_cofix_aux      term
  | FixUnfold   -> atomic_fix_aux        term
  | FunApply    -> atomic_fun_aux        term
  | DefUnfold   -> atomic_unfold_aux env term
  | LetUnfold   -> atomic_let_aux        term
  | MatchApply  -> atomic_match_aux      term

let apply_atomic_at env red (term: Constr.constr) pos : Constr.constr option =
  apply_at term pos (fun (x : Constr.constr) -> (apply_atomic env red x))

let apply_atomic_at_in_concl red pos =
  Proofview.Goal.enter
    (fun gl ->
      let env    = Proofview.Goal.env gl                              in
      let constr = EConstr.Unsafe.to_constr (Proofview.Goal.concl gl) in
      match apply_at constr pos (apply_atomic env red) with
      | Some v -> Tactics.change_concl (EConstr.of_constr v)
      | None   -> Tactics.change_concl (EConstr.of_constr constr)
    )

let apply_atomic_head_let_in_concl red = apply_atomic_at_in_concl red [LetInDef]

let atomic_cofix   = apply_atomic_head_let_in_concl CoFixUnfold
let atomic_fix     = apply_atomic_head_let_in_concl FixUnfold
let atomic_fun     = apply_atomic_head_let_in_concl FunApply
let atomic_unfold  = apply_atomic_head_let_in_concl DefUnfold
let atomic_let     = apply_atomic_head_let_in_concl LetUnfold
let atomic_match   = apply_atomic_head_let_in_concl MatchApply
let atomic_let_rev = atomic_no_env (atomic_let_aux)

(* TODO *)
(* let apply_atomic_auto term (pos: atomic_red_location) = *)
(* let apply_atomic_auto_at term (pos: atomic_red_location) = *)
(*   apply_at term pos apply_atomic_auto *)
(* let apply_atomic_auto_at_in_concl (pos: atomic_red_location) = *)
(*   (apply_to_concl apply_atomic_auto) pos *)
