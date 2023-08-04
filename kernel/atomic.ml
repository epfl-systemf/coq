(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module implements atomic reductions *)

let rec apply_at_pos term pos f : Constr.constr option =
  match pos with
  | [] -> Some (f term)
  | h::t ->
    match Constr.kind term with
    | Rel  _ -> None (* TODO @mbty ERR *)
    | Var  _ -> None (* TODO @mbty ERR *)
    | Meta _ -> None (* TODO @mbty ERR *)
    | Evar ((id, sl)) -> (* TODO @mbty ? *) (
      match SList.nth_option sl h with
      | Some (Some x) ->
        let new_slist =
          Option.bind (apply_at_pos x t f) (fun y -> SList.set_option sl h y)
        in Option.map (fun y -> Constr.of_kind (Evar ((id, y)))) new_slist
      | _ -> None (* TODO @mbty ERR *)
    )
    | Sort (_) -> None (* TODO @mbty ERR *)
    | Cast (c1, k, c2) -> (
      match h with
      | 0 ->
        Option.map
          (fun x -> Constr.of_kind (Cast (x, k, c2)))
          (apply_at_pos c1 t f)
      | 1 ->
        Option.map
          (fun x -> Constr.of_kind (Cast (c1, k, x)))
          (apply_at_pos c2 t f)
      | _ -> None (* TODO @mbty ERR *)
    )
    | Prod (bind_annot, c1, c2) -> (
      match h with
      | 0 ->
        Option.map
          (fun x -> Constr.of_kind (Prod (bind_annot, x, c2)))
          (apply_at_pos c1 t f)
      | 1 ->
        Option.map
          (fun x -> Constr.of_kind (Prod (bind_annot, c1, x)))
          (apply_at_pos c2 t f)
      | _ -> None (* TODO @mbty ERR *)
    )
    | Lambda (bind_annot, c1, c2) -> (
      match h with
      | 0 ->
        Option.map
          (fun x -> Constr.of_kind (Lambda (bind_annot, x, c2)))
          (apply_at_pos c1 t f)
      | 1 ->
        Option.map
          (fun x -> Constr.of_kind (Lambda (bind_annot, c1, x)))
          (apply_at_pos c2 t f)
      | _ -> None (* TODO @mbty ERR *)
    )
    | LetIn (bind_annot, c1, c2, c3) -> (
      match h with
      | 0 ->
        Option.map
          (fun x -> Constr.of_kind (LetIn (bind_annot, x, c2, c3)))
          (apply_at_pos c1 t f)
      | 1 ->
        Option.map
          (fun x -> Constr.of_kind (LetIn (bind_annot, c1, x, c3)))
          (apply_at_pos c2 t f)
      | 2 ->
        Option.map
          (fun x -> Constr.of_kind (LetIn (bind_annot, c1, c2, x)))
          (apply_at_pos c3 t f)
      | _ -> None (* TODO @mbty ERR *)
    )
    | App (c1, cx) -> (
      match h with
      | 0 ->
        Option.map (fun x -> Constr.of_kind (App (x, cx))) (apply_at_pos c1 t f)
      | n ->
        Option.map
          (fun x -> Constr.of_kind (App (c1, x)))
          (apply_in_arr cx (n - 1) t f)
    )
    | Const     _ -> None (* TODO @mbty ERR *)
    | Ind       _ -> None (* TODO @mbty ERR *)
    | Construct _ -> None (* TODO @mbty ERR *)
    | Case (
        case_info, univ, params_c1, (ret_binder, c2), pcase_invert_c3, c4,
        branches_c5
      ) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> (
          Option.map
            (fun x ->
              Constr.of_kind (Case (
                case_info, univ, x, (ret_binder, c2), pcase_invert_c3, c4,
                branches_c5
              ))
            )
            (apply_in_arr params_c1 h' t' f)
        )
      )
      | 1 -> (
        Option.map
          (fun x ->
            Constr.of_kind (Case (
              case_info, univ, params_c1, (ret_binder, x), pcase_invert_c3, c4,
              branches_c5
            ))
          )
          (apply_at_pos c2 t f)
      )
      | 2 -> (
        match pcase_invert_c3 with
        | NoInvert -> None (* TODO @mbty ERR *)
        | CaseInvert cx ->
          match t with
          | [] -> None (* TODO @mbty ERR *)
          | h'::t' ->
            Option.map
              (fun x ->
                Constr.of_kind (Case (
                  case_info, univ, params_c1, (ret_binder, c2),
                  CaseInvert {indices = x}, c4, branches_c5
                ))
              )
              (apply_in_arr cx.indices h' t' f)
      )
      | 3 -> (
        Option.map
          (fun x ->
            Constr.of_kind (Case (
              case_info, univ, params_c1, (ret_binder, x), pcase_invert_c3, x,
              branches_c5
            ))
          )
          (apply_at_pos c2 t f)
      )
      | 4 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> (
          Option.map
            (fun x ->
              Constr.of_kind (Case (
                case_info, univ, params_c1, (ret_binder, c2), pcase_invert_c3,
                c4, x
              ))
            )
            (apply_in_arr_snd branches_c5 h' t' f)
        )
      )
      | _ -> None (* TODO @mbty ERR *)
    )
    | Fix ((args, (binders, cx1, cx2))) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' ->
          Option.map
            (fun x -> Constr.of_kind (Fix ((args, (binders, x, cx2)))))
            (apply_in_arr cx1 h' t' f)
      )
      | 1 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' ->
          Option.map
            (fun x -> Constr.of_kind (Fix ((args, (binders, cx1, x)))))
            (apply_in_arr cx2 h' t' f)
      )
      | _ -> None  (* TODO @mbty ERR *)
    )
    | CoFix ((returned_comp, (binders, cx1, cx2))) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' ->
          Option.map
            (fun x ->
              Constr.of_kind (CoFix ((returned_comp, (binders, x, cx2))))
            )
            (apply_in_arr cx1 h' t' f)
      )
      | 1 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' ->
          Option.map
            (fun x ->
              Constr.of_kind (CoFix ((returned_comp, (binders, cx1, x))))
            )
            (apply_in_arr cx2 h' t' f)
      )
      | _ -> None  (* TODO @mbty ERR *)
    )
    | Proj (id, c) ->
      Option.map (fun x -> Constr.of_kind (Proj (id, x))) (apply_at_pos c pos f)
    | Int   _ -> None (* TODO @mbty ERR *)
    | Float _ -> None (* TODO @mbty ERR *)
    | Array (univ, cx, c1, c2) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' ->
          Option.map
            (fun x -> Constr.of_kind (Array (univ, x, c1, c2)))
            (apply_in_arr cx h' t' f)
      )
      | 1 ->
        Option.map
          (fun x -> Constr.of_kind (Array (univ, cx, x, c2)))
          (apply_at_pos c1 t f)
      | 2 ->
        Option.map
          (fun x -> Constr.of_kind (Array (univ, cx, c1, x)))
          (apply_at_pos c2 t f)
      | _ -> None (* TODO @mbty ERR *)
    )
and apply_in_arr arr n pos f =
  let item = (
    if (n < Array.length arr)
    then Some (Array.get arr n)
    else None (* TODO @mbty ERR *)
  ) in
  let item' = Option.bind item (fun x -> apply_at_pos x pos f) in
  Option.map (fun x -> Array.set arr n x; arr) item'
and apply_in_arr_snd arr n pos f =
  let item = (
    if (n < Array.length arr)
    then Some (Array.get arr n)
    else None (* TODO @mbty ERR *)
  ) in
  let item' =
    Option.bind
      item
      (fun x -> Option.map (fun y -> (fst x, y)) (apply_at_pos (snd x) pos f))
  in
  Option.map (fun x -> Array.set arr n x; arr) item'

let apply_appropriate_atomic env term =
  match Constr.kind term with
  (* Unfold cofixpoint once *)
  | CoFix ((id, ((binders, types, bodies) as fb))) ->
    let body  = bodies.(id) in
    let fixes =
      List.init
        (Array.length bodies)
        (fun id -> Constr.of_kind (CoFix (id, fb)))
    in
    Vars.substl fixes body
  (* Unfold fixpoint once *)
  (* TODO should rather make use of substnl, right? *)
  | Fix ((decreasing_arguments, id), ((binders, types, bodies) as fb)) ->
    let body  = bodies.(id) in
    let fixes =
      List.init
        (Array.length bodies)
        (fun id -> Constr.of_kind (Fix ((decreasing_arguments, id), fb)))
    in
    Vars.substl fixes body
  (* Apply function *)
  | App (what, args) ->
    (match (Constr.kind what) with
    | Lambda (lname, lype, lbody) ->
      (* TODO match tbl ou longueur liste *)
      (match Array.to_list args with
      | []    -> term
      | h::[] -> Vars.subst1 h lbody
      | h::t  -> Constr.of_kind (App ((Vars.subst1 h lbody), Array.of_list t)))
    | _ -> term)
  (* Unfold definition *)
  | Const (constant_info, universe_info) ->
    let pbody = (Environ.lookup_constant constant_info env).const_body in
    (match pbody with
    | Def v -> v
    | _ -> term
    )
  (* Undo let binding *)
  | LetIn (name_info, value, value_type, body) ->
    (match name_info.binder_name with
    | Name (id) -> Vars.(subst1 value (subst_var id body))
    | _ -> term)
  (* Apply pattern match *)
  (* TODO substnl offset? *)
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

let reduce_at_pos env term pos =
  match apply_at_pos term pos (apply_appropriate_atomic env) with
  | None   -> term
  | Some x -> x

let apply_hints env term hints =
  List.fold_left (fun acc hint -> reduce_at_pos env acc hint) term hints

let print_at term pos =
  match Constr.kind term with
  | Rel       _ -> "Rel"
  | Var       _ -> "Var"
  | Meta      _ -> "Meta"
  | Evar      _ -> "Evar"
  | Sort      _ -> "Sort"
  | Cast      _ -> "Cast"
  | Prod      _ -> "Prod"
  | Lambda    _ -> "Lambda"
  | LetIn     _ -> "LetIn"
  | App       _ -> "App"
  | Const     _ -> "Const"
  | Ind       _ -> "Ind"
  | Construct _ -> "Construct"
  | Case      _ -> "Case"
  | Fix       _ -> "Fix"
  | CoFix     _ -> "CoFix"
  | Proj      _ -> "Proj"
  | Int       _ -> "Int"
  | Float     _ -> "Float"
  | Array     _ -> "Array"

(* TODO @mbty should probably not be in kernel *)
let rec focus term pos =
  match pos with
  | [] -> Some (term)
  | h::t ->
    match Constr.kind term with
    | Rel  _ -> None (* TODO @mbty ERR *)
    | Var  _ -> None (* TODO @mbty ERR *)
    | Meta _ -> None (* TODO @mbty ERR *)
    | Evar ((id, sl)) -> (* TODO @mbty ? *) (
      match SList.nth_option sl h with
      | Some (Some x) -> focus x t
      | _ -> None (* TODO @mbty ERR *)
    )
    | Sort (_) -> None (* TODO @mbty ERR *)
    | Cast (c1, k, c2) -> (
      match h with
      | 0 -> focus c1 t
      | 1 -> focus c2 t
      | _ -> None (* TODO @mbty ERR *)
    )
    | Prod (bind_annot, c1, c2) -> (
      match h with
      | 0 -> focus c1 t
      | 1 -> focus c2 t
      | _ -> None (* TODO @mbty ERR *)
    )
    | Lambda (bind_annot, c1, c2) -> (
      match h with
      | 0 -> focus c1 t
      | 1 -> focus c2 t
      | _ -> None (* TODO @mbty ERR *)
    )
    | LetIn (bind_annot, c1, c2, c3) -> (
      match h with
      | 0 -> focus c1 t
      | 1 -> focus c2 t
      | 2 -> focus c3 t
      | _ -> None (* TODO @mbty ERR *)
    )
    | App (c1, cx) -> (
      match h with
      | 0 -> focus c1 t
      | n -> focus_in_arr cx (n - 1) t
    )
    | Const     _ -> None (* TODO @mbty ERR *)
    | Ind       _ -> None (* TODO @mbty ERR *)
    | Construct _ -> None (* TODO @mbty ERR *)
    | Case (
        case_info, univ, params_c1, (ret_binder, c2), pcase_invert_c3, c4,
        branches_c5
      ) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr params_c1 h' t'
      )
      | 1 -> focus c2 t
      | 2 -> (
        match pcase_invert_c3 with
        | NoInvert -> None (* TODO @mbty ERR *)
        | CaseInvert cx ->
          match t with
          | [] -> None (* TODO @mbty ERR *)
          | h'::t' -> focus_in_arr cx.indices h' t'
      )
      | 3 -> focus c2 t
      | 4 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr_snd branches_c5 h' t'
      )
      | _ -> None (* TODO @mbty ERR *)
    )
    | Fix ((args, (binders, cx1, cx2))) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr cx1 h' t'
      )
      | 1 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr cx2 h' t'
      )
      | _ -> None  (* TODO @mbty ERR *)
    )
    | CoFix ((returned_comp, (binders, cx1, cx2))) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr cx1 h' t'
      )
      | 1 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr cx2 h' t'
      )
      | _ -> None  (* TODO @mbty ERR *)
    )
    | Proj (id, c) ->
      Option.map (fun x -> Constr.of_kind (Proj (id, x))) (focus c pos)
    | Int   _ -> None (* TODO @mbty ERR *)
    | Float _ -> None (* TODO @mbty ERR *)
    | Array (univ, cx, c1, c2) -> (
      match h with
      | 0 -> (
        match t with
        | [] -> None (* TODO @mbty ERR *)
        | h'::t' -> focus_in_arr cx h' t'
      )
      | 1 -> focus c1 t
      | 2 -> focus c2 t
      | _ -> None (* TODO @mbty ERR *)
    )
and focus_in_arr arr n pos =
  if (n < Array.length arr)
  then focus (Array.get arr n) pos
  else None
and focus_in_arr_snd arr n pos =
  if (n < Array.length arr)
  then (focus (snd (Array.get arr n)) pos)
  else None (* TODO @mbty ERR *)
