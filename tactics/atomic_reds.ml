(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* TODO In the process of being moved to kernel, will be removed from tactics
   eventually. tactics.ml should call the functions defined by the kernel. *)

type atomic_red =
| AtomicFun    (* function   application | beta  reduction *)
| AtomicFix    (* fixpoint   expansion   | fix   reduction *)
| AtomicCoFix  (* cofixpoint expansion   | cofix reduction *)
| AtomicMatch  (* match      reduction   | match reduction *)
| AtomicLet    (* let-in     reduction   | zeta  reduction *)
| AtomicUnfold (* definition expansion   | delta reduction *)

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

(* Cofixpoint unfolding *)
let atomic_cofix_aux term =
  match Constr.kind term with
  | CoFix ((id, ((binders, types, bodies) as fb))) ->
    let body  = bodies.(id) in
    let fixes =
      List.init
        (Array.length bodies)
        (fun id -> Constr.of_kind (CoFix (id, fb)))
    in
    Some (Vars.substl fixes body)
  | _ -> None

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
    Some (Vars.substl fixes body)
  | App (what, args) ->
   (match (Constr.kind what) with
    | Fix ((decreasing_arguments, id), ((binders, types, bodies) as fb)) ->
      let body  = bodies.(id) in
      let fixes =
        List.init
          (Array.length bodies)
          (fun id -> Constr.of_kind (Fix ((decreasing_arguments, id), fb)))
      in
      Some (Constr.of_kind (App (Vars.substl fixes body, args)))
    | _ -> None)
  | _ -> None

(* Lambda application *)
let atomic_fun_aux term =
  match Constr.kind term with
  | App (what, args) ->
    (match (Constr.kind what) with
    | Lambda (lname, lype, lbody) ->
      (* TODO match tbl ou longueur liste *)
      (match Array.to_list args with
      | []    -> None
      | h::[] -> Some (Vars.subst1 h lbody)
      | h::t  ->
        Some (Constr.of_kind (App ((Vars.subst1 h lbody), Array.of_list t))))
    | _ -> None)
  | _ -> None

(* Definition unfolding *)
let atomic_unfold_aux env term =
  match Constr.kind term with
  | Const (constant_info, universe_info) ->
    let pbody = (Environ.lookup_constant constant_info env).const_body in
    (match pbody with
    | Def v -> Some v
    | _ -> None (* TODO What about other constructors? *)
    )
  | _ -> None

(* Let unfolding *)
let atomic_let_aux term =
  match Constr.kind term with
  | LetIn (name_info, value, value_type, body) ->
    (match name_info.binder_name with
    | Name (id) -> Some (Vars.(subst1 value (subst_var id body)))
    | _ -> None)
  | _ -> None

let atomic_let_wrapped term =
  match atomic_let_aux term with
  | None   -> term
  | Some v -> v

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
       Some (snd branches_info.(constructor_id - 1))
     | App (what, args) ->
       (match Constr.kind what with
        | Construct ((type_info, constructor_id), construct_universe_info) ->
          let (branch_args, branch_body) = branches_info.(constructor_id - 1) in
          let vars =
            List.combine (Array.to_list branch_args) (Array.to_list args)
          in
          Some
            (match List.length vars with
            | 0 -> Constr.of_kind (Rel 1)
            | _ -> Vars.substl (List.rev (Array.to_list args)) branch_body
            )
        | _ -> None
       )
     | _ -> None
    )
  | _ -> None

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

type atomic_red_direction =
| LetInDef
type atomic_red_location = atomic_red_direction list
let default_location = [LetInDef]

(* TODO partial implementation, see above for the incomplete fuller version *)
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
  let res =
    match red with
    | AtomicCoFix  -> atomic_cofix_aux      term
    | AtomicFix    -> atomic_fix_aux        term
    | AtomicFun    -> atomic_fun_aux        term
    | AtomicUnfold -> atomic_unfold_aux env term
    | AtomicLet    -> atomic_let_aux        term
    | AtomicMatch  -> atomic_match_aux      term
  in
  match res with
  | None   -> term
  | Some v -> v

(* The presence of a proof context can't be assumed when using eval *)
let eval_interface red : Reductionops.e_reduction_function =
  (fun env evar_map term ->
    (
      evar_map,
      let eterm = EConstr.Unsafe.to_constr term in
      let res = Option.map EConstr.of_constr (
        match red with
        | AtomicCoFix  -> atomic_cofix_aux      eterm
        | AtomicFix    -> atomic_fix_aux        eterm
        | AtomicFun    -> atomic_fun_aux        eterm
        | AtomicUnfold -> atomic_unfold_aux env eterm
        | AtomicLet    -> atomic_let_aux        eterm
        | AtomicMatch  -> atomic_match_aux      eterm
      ) in
      match res with
      | Some x -> x
      | None -> term
    )
  )

let trivial_test () : unit Find_subterm.testing_function = {
  match_fun = (fun () _ -> ());
  merge_fun = (fun () _ -> ());
  testing_state = ();
  last_found = None
}

(* TODO @mbty import apply auto from kernel *)

let apply_atomic_occs' env red t occs evar_map =
  let test = trivial_test () in
  let bywhat () =
    match test.last_found with
    | None        -> failwith "TODO @mbty (not supposed to happen)"
    | Some (_, t') ->
      EConstr.of_constr (apply_atomic env red (EConstr.Unsafe.to_constr t'))
  in
  Find_subterm.replace_term_occ_modulo env evar_map occs test bywhat t

let apply_atomic_occs env red t occs evar_map =
  Some (apply_atomic_occs' env red t occs evar_map)
