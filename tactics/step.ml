open Pp
open CErrors
open Result
open Environ
open Names
open Constr
open Vars
open Primred
open Inductive

(* do not use repeat step cbv, but let rec rscbv () := try (step cbv; rscbv ()) in rscbv () *)

(* match let bindings should not be a thing, it should be a syntax that adds lets at the start of the branch or a syntactic sugar that is completely expanded *)

(* UTILITY *)

let map_left2 f1 f2 a1 a2 =
  let l = Array.length a1 in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f1 a1.(0)) in
    let s = Array.make l (f2 a1.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f1 a1.(i);
      s.(i) <- f2 a2.(i)
    done;
    r, s
  end

let array_with a n x = let a = Array.copy a in a.(n) <- x; a

let or_step f x g =
  match x with
  | Some x -> Some (f x)
  | None -> g ()

let or_else x f =
  match x with
  | None -> f ()
  | _ -> x

let for_step f e =
  let rec aux i = if i = e then None else or_else (f i) (fun _ -> aux (i + 1))
  in aux

let array_step_n f a =
  for_step (fun i -> Option.map (array_with a i) (f a.(i))) (Array.length a)

let array_step f a = array_step_n f a 0

let slist_step f =
  let open SList in
  let rec aux = function
  | Nil -> None
  | Default (n, t) -> Option.map (defaultn n) (aux t)
  | Cons (h, t) -> or_step (fun h -> cons h t) (f h) (fun _ -> Option.map (cons h) (aux t))
  in aux

let force msg = function
| Some x -> x
| None -> user_err (str msg)


(* ESSENTIALS *)

module KNativeEntries =
  struct
    type elem = constr
    type args = constr array
    type evd = unit
    type uinstance = UVars.Instance.t
    open UnsafeMonomorphic

    let get = Array.unsafe_get

    let get_int () e =
      match kind e with
      | Int i -> i
      | _ -> raise NativeDestKO

    let get_float () e =
      match kind e with
      | Float f -> f
      | _ -> raise NativeDestKO

    let get_string () e =
      match kind e with
      | String s -> s
      | _ -> raise NativeDestKO

    let get_parray () e =
      match kind e with
      | Array (_, t, def, _) -> Parray.of_array t def
      | _ -> raise NativeDestKO

    let mkInt _ = mkInt

    let mkFloat _ = mkFloat

    let mkString _ = mkString

    let mkBool env b =
      let ct, cf = get_bool_constructors env in
      mkConstruct (if b then ct else cf)

    let mkCarry env b e =
      let int_ty = mkConst @@ get_int_type env in
      let c0, c1 = get_carry_constructors env in
      mkApp (mkConstruct (if b then c1 else c0), [| int_ty; e |])

  let mkIntPair env e1 e2 =
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp (mkConstruct c, [| int_ty; int_ty; e1; e2 |])

  let mkFloatIntPair env f i =
    let float_ty = mkConst @@ get_float_type env in
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp (mkConstruct c, [| float_ty; int_ty; f; i |])

  let mkLt env =
    let _, lt, _ = get_cmp_constructors env in
    mkConstruct lt

  let mkEq env =
    let eq, _, _ = get_cmp_constructors env in
    mkConstruct eq

  let mkGt env =
    let _, _, gt = get_cmp_constructors env in
    mkConstruct gt

  let mkFLt env =
    let _, lt, _, _ = get_f_cmp_constructors env in
    mkConstruct lt

  let mkFEq env =
    let eq, _, _, _ = get_f_cmp_constructors env in
    mkConstruct eq

  let mkFGt env =
    let _, _, gt, _ = get_f_cmp_constructors env in
    mkConstruct gt

  let mkFNotComparable env =
    let _, _, _, nc = get_f_cmp_constructors env in
    mkConstruct nc

  let mkPNormal env =
    let pNormal, _, _, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pNormal

  let mkNNormal env =
    let _, nNormal, _, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct nNormal

  let mkPSubn env =
    let _, _, pSubn, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pSubn

  let mkNSubn env =
    let _, _, _, nSubn, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct nSubn

  let mkPZero env =
    let _, _, _, _, pZero, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pZero

  let mkNZero env =
    let _, _, _, _, _, nZero, _, _, _ = get_f_class_constructors env in
    mkConstruct nZero

  let mkPInf env =
    let _, _, _, _, _, _, pInf, _, _ = get_f_class_constructors env in
    mkConstruct pInf

  let mkNInf env =
    let _, _, _, _, _, _, _, nInf, _ = get_f_class_constructors env in
    mkConstruct nInf

  let mkNaN env =
    let _, _, _, _, _, _, _, _, nan = get_f_class_constructors env in
    mkConstruct nan

  let mkArray env u t ty =
    let t, def = Parray.to_array t in
    mkArray (u, t, def, ty)

  end

module KredNative = RedNative(KNativeEntries)

let substn x =
  let rec aux n c =
    match kind c with
    | Rel i -> if Int.equal i n then x else c
    | _ -> map_with_binders succ aux n c
  in aux

let unlift c =
  let rec aux n c =
    match kind c with
    | Rel i ->
      ( match () with
        | () when i < n -> c
        | () when i > n -> mkRel (i - 1)
        | () -> raise DestKO
      )
    | _ -> map_with_binders succ aux n c
  in try Some (aux 1 c) with DestKO -> None

(* Term zipper
let rec slist_rev_append acc = function
| SList.Nil -> acc
| SList.Cons h t -> slist_rev_append (SList.cons h acc) t
| SList.Default n t -> slist_rev_append (SList.defaultn n acc) t

type zipper_of_term =
| ZEvar      of Evar.t * constr SList.t * constr SList.t
| ZCast      of cast_kind * types
| ZProd1     of (Name.t, Sorts.relevance) Context.pbinder_annot * types
| ZProd2     of (Name.t, Sorts.relevance) Context.pbinder_annot * types
| ZLambdaT   of (Name.t, Sorts.relevance) Context.pbinder_annot * constr
| ZLambdaC   of (Name.t, Sorts.relevance) Context.pbinder_annot * types
| ZLetInT    of (Name.t, Sorts.relevance) Context.pbinder_annot * constr * constr
| ZLetInC1   of (Name.t, Sorts.relevance) Context.pbinder_annot * types * constr
| ZLetInC2   of (Name.t, Sorts.relevance) Context.pbinder_annot * constr * types
| ZAppH      of constr array
| ZAppA      of constr * (int * constr array)
| ZCaseP     of
  case_info *
  UVars.Instance.t *
  (int * constr array) *
  (types, Sorts.relevance) pcase_return *
  constr pcase_invert *
  constr *
  (constr, Sorts.relevance) pcase_branch array
| ZCaseR     of
  case_info *
  UVars.Instance.t *
  constr array *
  ((Name.t, Sorts.relevance) Context.pbinder_annot array * Sorts.relevance) *
  constr pcase_invert *
  constr *
  (constr, Sorts.relevance) pcase_branch array
| ZCaseM     of
  case_info *
  UVars.Instance.t *
  constr array *
  (types, Sorts.relevance) pcase_return *
  constr pcase_invert *
  (constr, Sorts.relevance.t) pcase_branch array
| ZCaseB     of
  case_info *
  UVars.Instance.t *
  constr array *
  (types, Sorts.relevance) pcase_return *
  constr pcase_invert *
  constr *
  (int * (constr, Sorts.relevance) pcase_branch array)
| ZFixT      of (int array * int) * ((Name.t, Sorts.relevance) pbinder_annot array * (int * types array) * constr array)
| ZFixC      of (int array * int) * ((Name.t, Sorts.relevance) pbinder_annot array * types array * (int * constr array))
| ZCoFixT    of int * ((Name.t, Sorts.relevance) pbinder_annot array * (int * types array) * constr array)
| ZCoFixC    of int * ((Name.t, Sorts.relevance) pbinder_annot array * types array * (int * constr array))
| ZProj      of Projection.t * Sorts.relevance
| ZArrayT    of UVars.Instance.t * constr array * constr
| ZArrayD    of UVars.Instance.t * constr array * types
| ZArrayC    of UVars.Instance.t * (int * constr array) * constr * types

let unzip_one x = function
| ZEvar (ev, l, r) -> mkEvar (ev, slist_rev_append l (SList.cons x r))
| ZCast (k, t) -> mkCast (x, k, t)
| ZProd1 (na, t) -> mkProd (na, x, t)
| ZProd2 (na, t) -> mkProd (na, t, x)
| ZLambdaT (na, c) -> mkLambda (na, x, c)
| ZLambdaC (na, t) -> mkLambda (na, t, x)
| ZLetInT (na, b, c) -> mkLetIn (na, b, x, c)
| ZLetInC1 (na, t, c) -> mkLetIn (na, x, t, c)
| ZLetInC2 (na, b, t) -> mkLetIn (na, b, t, x)
| ZAppH args -> mkApp (x, args)
| ZAppA (head, n, args) -> mkApp (head, array_with args n x))
| ZCaseP (ci, u, (n, pms), p, iv, c, brs) -> mkCase (ci, u, array_with pms n x, p, iv, c, brs)
| ZCaseR (ci, u, pms, (nas, r), iv, c, brs) -> mkCase (ci, u, pms, ((nas, x), r), iv, c, brs)
| ZCaseM (ci, u, pms, p, iv, brs) -> mkCase (ci, u, pms, p, iv, x, brs)
| ZCaseB (ci, u, pms, p, iv, c, (n, brs)) ->
  mkCase (ci, u, pms, p, iv, c, let nas, br = brs.(n) in array_with brs n (nas, x))
| ZFixT (si, (nas, (n, tys), bds) -> mkFix (si, (nas, array_with tys n x, bds))
| ZFixC (si, (nas, tys, (n, bds)) -> mkFix (si, (nas, tys, array_with bds n x))
| ZCoFixT (ri, (nas, (n, tys), bds) -> mkCoFix (ri, (nas, array_with tys n x, bds))
| ZCoFixC (ri, (nas, tys, (n, bds)) -> mkCoFix (ri, (nas, tys, array_with bds n x))
| ZProj (pn, r) -> mkProj (pn, r, x)
| ZArrayT (u, ts, def) -> mkArray (u, ts, def, x)
| ZArrayD (u, ts, ty) -> mkArray (u, ts, x, ty)
| ZArrayC (u, (n, ts), def, ty) -> mkArray (u, array_with ts n x, def, ty)

let unzip_term = List.fold_left unzip_one
*)


(* COMMON REDUCTION PROCEDURES *)

(* No need to case on args, of_kind already ensures invariants *)
let beta_red head args = mkApp (subst1 args.(0) head, CArray.tl args)

let delta_prim_red env (op, u) args =
  let nargs = CPrimitives.arity op in
  let len = Array.length args in
  let fred args =
    match KredNative.red_prim env () op u args with
    | Some x -> Ok x
    | None -> Error "primitive cannot be reduced with provided arguments"
  in
  ( match () with
    | () when len < nargs -> Error "primitive applied to too few arguments"
    | () when len > nargs ->
      Result.map
        (fun head -> mkApp (head, Array.sub args nargs (len - nargs)))
        (fred (Array.sub args 0 nargs))
    | () -> fred args
  )

let delta_var_red env id =
  match lookup_named id env with
  | LocalDef (_, c, _) -> Some c
  | LocalAssum _  -> None

let delta_const_red env sp =
  try Ok (constant_value_in env sp)
  with NotEvaluableConst x -> Error x

let eta_prime_red evm env t c =
  try
    let head, args = destApp c in
    let nargs = Array.length args in
    let arg = args.(nargs - 1) in
    if not (isRelN 1 arg) then Error "Argument of the application under abstraction is not the bound variable." else
    match unlift (if nargs = 1 then head else mkApp (head, Array.sub args 0 (nargs - 1))) with
    | None -> Error "Variable bound by the abstraction is used more than once."
    | Some c ->
      let tyc = Retyping.get_type_of env evm (EConstr.of_constr c) in
      let _, k, _ = EConstr.destProd evm tyc in
      if Reductionops.is_conv env evm (EConstr.of_constr t) k
      then Ok c
      else Error "Performing eta reduction would change type."
  with DestKO -> Error "Term under abstraction is not an application."

let is_fix_reducible env ((reci, i), _) args =
  let argi = reci.(i) in
  argi < Array.length args &&
    match kind args.(argi) with
    | Construct _ -> true
    | App (head, _) -> isConstruct head
    | Const (kn, _) ->
      ( match (lookup_constant kn env).const_body with
        | Symbol true -> true (* Unholy rewrite get out of this kernel *)
        | _ -> false
      )
    | _ -> false

let fix_red env f args =
  if is_fix_reducible env f args
  then Some (mkApp (contract_fix f, args))
  else None

let proj_red pn args =
  let n = Projection.(npars pn + arg pn) in
  if n >= Array.length args then anomaly (str "Struct members missing.");
  args.(n)

let match_red env ci u c brs args =
  let nbrs = Array.length brs in
  if nbrs < c then anomaly (str "Not a constructor of the matched type.");
  let pms, args = CArray.chop ci.ci_npar args in
  let mind = lookup_mind_specif env ci.ci_ind in
  let br = expand_branch mind (ci, u, pms, (([||], mkProp), Sorts.Relevant), NoInvert, mkProp, brs) (c - 1) in
  mkApp (br, args)

let match_uip_red_specif env (mib, mip) u pms indices = function
| [||] -> None
| [| [||] , br |] ->
  let open Declarations in
  let expect_indices =
    try snd (destApp (snd mip.mind_nf_lc.(0)))
    with DestKO -> [||]
  in
  let nind = Array.length indices in
  let rec loop i =
    if Int.equal nind i then true else
    let expected = expect_indices.(mib.mind_nparams + i) in
    let expected = Vars.substl pms expected in
    match Conversion.conv env expected indices.(i) with
    | Ok () -> loop (i + 1)
    | Error () -> false
  in
  if loop 0 then Some br else None
| _ -> anomaly (str "UIP on a type which doesn't have a unique constructor.")

let match_uip_red env ci u pms indices brs =
  let mind = lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  match_uip_red_specif env mind u ps indices brs

(* Zeta in match bindings (breaks property of "one location = one reduction") and one-stepping now becomes harder *)
let zeta_match_red br nas brs c brn n =
  let br' = substn c n br in
  if br == br' then None else Some (array_with brs brn (nas, br'))

(* primitive projection eta reduction *)
let projsurj_red env ind args =
  let get_record n c =
    let pn, _, bdy = destProj c in
    if not (eq_ind_chk (Projection.inductive pn) ind) || Projection.arg pn != n then raise DestKO;
    bdy
  in
  let mib = lookup_mind (fst ind) env in
  Result.bind
    ( match mib.mind_record with
      | PrimRecord x -> let _, x, _, _ = x.(snd ind) in Ok (Array.length x)
      | _ -> Error "Not a record constructor."
    )
    ( fun nproj ->
      let nargs = Array.length args in
      if mib.mind_nparams + nproj != nargs then Error "Record constructor applied to too few arguments." else
      try
        let base_c = get_record 0 args.(mib.mind_nparams) in
        let rec arg_loop n =
          let cn = n - mib.mind_nparams in
          if cn = 0 then Ok base_c else
          if Constr.equal (get_record cn args.(n)) base_c
          then arg_loop (n - 1)
          else Error "Terms under projections are not the same."
        in
        arg_loop (nargs - 1)
      with DestKO -> Error "Wrong projection."
    )

(* HEAD AND REDUCTION STRATEGY HELPERS *)

let app_head env head args =
  match kind head with
  | Lambda (_, _, c) -> Some (beta_red c args)
  | Fix f -> fix_red env f args
  | Const (c, u) ->
    Option.bind (get_primitive env c)
      (fun op -> Result.to_option (delta_prim_red env (op, u) args))
  | Construct ((ind, _), _) -> Result.to_option (projsurj_red env ind args)
  | _ -> None

let const_head env sp =
  match delta_const_red env sp with
  | Ok x -> Some x
  | Error (HasRules _) -> Feedback.msg_warning (str "Cannot reduce symbols."); None (* Rules should be removed from Rocq *)
  | Error _ -> None

let match_head env ci u pms bi iv c brs =
  match kind c with
  | Construct ((_, c), _) -> Some (match_red env ci u c brs [||])
  | CoFix cf -> Some (mkCase (ci, u, pms, bi, iv, contract_cofix cf, brs))
  | App (head, args) ->
    ( match kind head with
      | Construct ((_, c), _) -> Some (match_red env ci u c brs args)
      | CoFix cf -> Some (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs))
      | _ -> None
    )
  | _ -> None

let zeta_match_head env ci u pms brs =
  let mind = Inductive.lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  for_step
    ( fun i ->
      let nargs = ci.ci_cstr_nargs.(i) in
      let ndecls = ci.ci_cstr_ndecls.(i) in
      if nargs = ndecls then None else
      let ctx = expand_branch_context mind u ps brs i in
      let nas, br = brs.(i) in
      let rec bind_mapper n = let open Context.Rel.Declaration in function
      | [] -> None
      | LocalAssum _ :: t -> bind_mapper (n + 1) t
      | LocalDef (_, c, _) :: t ->
        or_else (zeta_match_red br nas brs c i n) (fun _ -> bind_mapper (n + 1) t)
      in
      bind_mapper 1 ctx
    )
    (Array.length brs)
    0

let proj_head pn r c =
  if Projection.unfolded pn
  then
    ( match kind c with
      (* Construct impossible because `proj {||}` and `proj {| proj := |}` are not a thing *)
      | Construct _ -> anomaly (str "Projection on an empty struct.")
      | CoFix cf -> Some (mkProj (pn, r, contract_cofix cf))
      | App (head, args) ->
        ( match kind head with
          | Construct _ -> Some (proj_red pn args)
          | CoFix cf -> Some (mkProj (pn, r, mkApp (contract_cofix cf, args)))
          | _ -> None
        )
      | _ -> None
    )
  else Some (mkProj (Projection.unfold pn, r, c))

(* TREE WALKER *)

let map_constr_with_binders_left_to_right env g f acc c =
  let open Context.Rel.Declaration in
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> c
  | Cast (b, k, t) ->
    let b' = f acc b in
    if b' == b then c else mkCast (b', k, t)
  | Prod (na, t, b) ->
    let t' = f acc t in
    let b' = f (g (LocalAssum (na,t)) acc) b in
    if t' == t && b' == b then c else mkProd (na, t', b')
  | Lambda (na, t, b) ->
    let t' = f acc t in
    let b' = f (g (LocalAssum (na,t)) acc) b in
    if t' == t && b' == b then c else mkLambda (na, t', b')
  | LetIn (na, bo, t, b) ->
    let bo' = f acc bo in
    let t' = f acc t in
    let b' = f (g (LocalDef (na,bo,t)) acc) b in
    if bo' == bo && t' == t && b' == b then c else mkLetIn (na, bo', t', b')
  | App (h, al) ->
    let h' = f acc h in
    let al' = CArray.map_left (f acc) al in
    if h == h' && Array.for_all2 (==) al al' then c else mkApp (h', al')
  | Proj (p, r, b) ->
    let b' = f acc b in
    if b' == b then c else mkProj (p, r, b')
  | Evar (ev, ctx) ->
    let ctx' = SList.Smart.map (fun c -> f acc c) ctx in
    if ctx' == ctx then c else mkEvar (ev, ctx')
  | Case (ci, u, pms, (p, r), iv, b, bl) ->
	let mind = lookup_mind_specif env ci.ci_ind in
    let p0, bl0 = Environ.expand_case_contexts mind (ci.ci_ind, u) pms (fst p) bl in
    let f_ctx (nas, c as r) ctx =
      let c' = f (List.fold_right g ctx acc) c in
      if c' == c then r else (nas, c')
    in
    let b' = f acc b in
    let pms' = CArray.map_left (f acc) pms in
    let p' = f_ctx p p0 in
    let bl' = CArray.map_left (fun (c, c0) -> f_ctx c c0) (Array.map2 (fun x y -> (x, y)) bl bl0) in
    if b' == b && pms' == pms && p' == p && bl' == bl then c
    else mkCase (ci, u, pms', (p', r), iv, b', bl')
  | Fix (ln, (lna, tl, bl)) ->
    let ctxt = CArray.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna tl in
    let acc' = Array.fold_left (fun e assum -> g assum e) acc ctxt in
    let tl', bl' = map_left2 (f acc) (f acc') tl bl in
    if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl' then c
    else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln, (lna, tl, bl)) ->
    let ctxt = CArray.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna tl in
    let acc' = Array.fold_left (fun e assum -> g assum e) acc ctxt in
    let tl', bl' = map_left2 (f acc) (f acc') tl bl in
    if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl' then c
    else mkCoFix (ln, (lna, tl', bl'))
  | Array(u, t, def, ty) ->
    let t' = CArray.map_left (f acc) t in
    let def' = f acc def in
    let ty' = f acc ty in
    if def' == def && t' == t && ty' == ty then c
    else mkArray (u, t', def', ty')

(* based on e_contextually, prep does matching and pre-processing, f does the reduction *)
let reduce_with_context occs prep f env t =
  let count = ref (Locusops.initialize_occurrence_counter occs) in
  let rec traverse nested env t =
    if Locusops.occurrences_done !count then (* Shortcut *) t else
    let cont nested = map_constr_with_binders_left_to_right env push_rel (traverse nested) env t in
    match prep env t with
    | None -> cont nested
    | Some payload ->
      let ok, count' = Locusops.update_occurrence_counter !count in
      count := count';
      if not ok then cont nested else
      match nested with
      | Some n ->
        user_err
          ( str "The subterm at occurrence "
            ++ int n
            ++ str " overlaps with the subterm at occurrence "
            ++ int (Locusops.current_occurrence !count)
            ++ str "."
          )
      | None -> (* Skip inner occurrences for stable counting of occurrences *)
        if Locusops.more_specific_occurrences !count
        then ignore (cont (Some (Locusops.current_occurrence !count)));
        f payload
  in
  let t = traverse None env t in
  Locusops.check_used_occurrences !count;
  t

(* REDUCTION TACTICS *)

let cast_prep _ c =
  match kind c with
  | Cast (ct, _, _) -> Some ct
  | _ -> None

let cast_step c = c

let beta_prep env c =
  try
    let head, args = destApp c in
    let _, _, c = destLambda head in
    Some (c, args)
  with DestKO -> None

let beta_step (head, args) = beta_red head args

let zeta_prep _ c =
  match kind c with
  | LetIn (_, b, _, c) -> Some (b, c)
  | _ -> None

let zeta_step (b, c) = subst1 b c

let zeta_match_prep ty brn n env c =
  match kind c with
  | Case (ci, u, pms, bi, iv, c, brs) when eq_ind_chk ty ci.ci_ind ->
    Some (env, ci, u, pms, bi, iv, c, brs)
  | _ -> None

let zeta_match_step brn n (env, ci, u, pms, bi, iv, c, brs) =
  let nas, br = brs.(brn) in
  let mind = lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  let binds = expand_branch_context mind u ps brs brn in
  let bind = match List.nth binds n with LocalDef (_, c, _) -> c | _ -> assert false in
  let brs =
    force "Match let binding is already reduced."
      (zeta_match_red br nas brs bind brn (n + 1)) in
  mkCase (ci, u, pms, bi, iv, c, brs)

type delta_kind =
| DeltaVar of variable
| DeltaConst of (constr, const_evaluation_result) result
| DeltaPrim of (CPrimitives.t * UVars.Instance.t) * constr array
| DeltaProj of Projection.t * Sorts.relevance * constr

(* reduction in prep to avoid matching a primitive *)
let delta_const_accept_prim env c =
  match delta_const_red env c with
  | Error (IsPrimitive _) -> None
  | x -> Some (env, DeltaConst x)

(* primitive resolution in prep to avoid counting constants twice *)
let delta_prim_reject_const env c u args =
  Option.map (fun op -> env, DeltaPrim ((op, u), args)) (get_primitive env c)

let delta_prep e env c =
  let open Evaluable in
  match kind c, e with
  | Var id, Some (EvalVarRef i) when Id.equal id i -> Some (env, DeltaVar id)
  | Var id, None -> Some (env, DeltaVar id)
  | Const (c, u), Some (EvalConstRef cr) when QConstant.equal env cr c ->
    delta_const_accept_prim env (c, u)
  | Const (c, u), None -> delta_const_accept_prim env (c, u)
  | Proj (pn, _, _), _ when Projection.unfolded pn -> None
  | Proj (pn, r, c), Some (EvalProjectionRef p)
    when QProjection.Repr.equal env p (Projection.repr pn) ->
    Some (env, DeltaProj (pn, r, c))
  | Proj (pn, r, c), None -> Some (env, DeltaProj (pn, r, c))
  | App (head, args), Some (EvalConstRef cr) ->
    ( match kind head with
      | Const (c, u) when QConstant.equal env cr c ->
        delta_prim_reject_const env c u args
      | _ -> None
    )
  | App (head, args), None ->
    ( match kind head with
      | Const (c, u) -> delta_prim_reject_const env c u args
      | _ -> None
    )
  | _ -> None

let delta_step = function
| env, DeltaVar id -> force "Variable has no unfoldable definition." (delta_var_red env id)
| _, DeltaConst (Ok c) -> c
| _, DeltaConst (Error Opaque) -> user_err (str "Constant is opaque.")
| _, DeltaConst (Error NoBody) -> user_err (str "Constant has no definition.")
| _, DeltaConst (Error (HasRules _)) ->
  user_err (str "Constant is a symbol with custom rewrite rules.")
| _, DeltaConst (Error (IsPrimitive _)) -> assert false (* don't try to unfold unapplied primitive *)
| env, DeltaPrim (p, args) ->
  ( match delta_prim_red env p args with
    | Ok x -> x
    | Error x -> user_err (str ("Could not reduce primitive: " ^ x ^ "."))
  )
| env, DeltaProj (pn, r, c) -> mkProj (Projection.unfold pn, r, c)

let eta_step evm env c =
  match kind (EConstr.Unsafe.to_constr (snd (Typing.type_of env evm (EConstr.of_constr c)))) with
  | Prod (na, k, _) -> mkLambda (na, k, mkApp (lift 1 c, [| mkRel 1 |]))
  | _ -> user_err (str "Head is not a function.")

let eta_prime_prep env c =
  match kind c with
  | Lambda (_, t, c) -> Some (env, Either.Left (t, c))
  | App (head, args) ->
    ( match kind head with
      | Construct ((ind, _), _) -> Some (env, Either.Right (ind, args))
      | _ -> None
    )
  | _ -> None

let eta_prime_step evm = function
| env, Either.Left (t, c) ->
  ( match eta_prime_red evm env t c with
    | Ok x -> x
    | Error m -> user_err (str m)
  )
| env, Either.Right (ind, args) ->
  ( match projsurj_red env ind args with
    | Ok x -> x
    | Error x -> user_err (str x)
  )

let evar_prep _ c =
  match kind c with
  | Evar ev -> Some ev
  | _ -> None

let evar_step evm ev =
  force "Evar has no unfoldable definition." (Evd.existential_opt_value0 evm ev)

let fix_prime_prep _ c =
  match kind c with
  | Fix f -> Some f
  | _ -> None

let fix_prep env c =
  try
    let head, args = destApp c in
    let f = destFix head in
    Some (env, f, args)
  with DestKO -> None

let fix_step (env, f, args) =
  force "Fixpoint is not reducible." (fix_red env f args)

let cofix_prime_prep _ c =
  match kind c with
  | CoFix cf -> Some cf
  | _ -> None

let cofix_prep _ c =
  match kind c with
  | Proj (pn, r, c) ->
    ( match kind c with
      | CoFix cf -> Some (Either.Left (pn, r, cf, [||]))
      | App (head, args) ->
        ( match kind head with
          | CoFix cf -> Some (Either.Left (pn, r, cf, args))
          | _ -> None
        )
      | _ -> None
    )
  | Case (ci, u, pms, bi, iv, c, brs) ->
    ( match kind c with
      | CoFix cf -> Some (Either.Right (ci, u, pms, bi, iv, cf, [||], brs))
      | App (head, args) ->
        ( match kind head with
          | CoFix cf -> Some (Either.Right (ci, u, pms, bi, iv, cf, args, brs))
          | _ -> None
        )
      | _ -> None
    )
  | _ -> None

let cofix_step = function
| Either.Left (pn, r, cf, args) -> mkProj (pn, r, mkApp (contract_cofix cf, args))
| Either.Right (ci, u, pms, bi, iv, cf, args, brs) ->
  mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs)

let match_prep env c =
  match kind c with
  | Proj (pn, r, c) when Projection.unfolded pn ->
    ( match kind c with
      (* Construct impossible because primitive have at least one projection *)
      | App (head, args) when isConstruct head -> Some (Either.Left (pn, args))
      | _ -> None
    )
  | Case (ci, u, pms, bi, iv, c, brs) ->
    ( match kind c with
      | Construct ((_, c), _) -> Some (Either.Right (env, ci, u, c, brs, [||]))
      | App (head, args) ->
        ( match kind head with
          | Construct ((_, c), _) -> Some (Either.Right (env, ci, u, c, brs, args))
          | _ -> None
        )
      | _ -> None
    )
  | _ -> None

let match_step = function
| Either.Left (pn, args) -> proj_red pn args
| Either.Right (env, ci, u, c, brs, args) -> match_red env ci u c brs args

let match_uip_prep env c =
  match kind c with
  | Case (ci, u, pms, _, CaseInvert {indices}, _, brs) ->
    Some (env, ci, u, pms, indices, brs)
  | _ -> None

let match_uip_step (env, ci, u, pms, indices, brs) =
  force "Matched type with UIP has wrong indices." (match_uip_red env ci u pms indices brs)

let head_step evm env c =
  match kind c with
  | Var id -> delta_var_red env id
  | Evar ev -> Evd.existential_opt_value0 evm ev
  | Cast (ct, _, _) -> Some ct
  | LetIn (na, b, u, c) -> Some (subst1 b c)
  | App (head, args) -> app_head env head args
  | Const sp -> const_head env sp
  | Case (ci, u, pms, bi, iv, c, brs) ->
    or_else (match_head env ci u pms bi iv c brs)
      ( fun _ ->
        or_else
          ( match iv with
            | CaseInvert {indices} -> match_uip_red env ci u pms indices brs
            | _ -> None
          )
          ( fun _ ->
            Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
              (zeta_match_head env ci u pms brs)
          )
      )
  | Proj (pn, r, c) -> proj_head pn r c
  | Lambda (_, t, c) -> Result.to_option (eta_prime_red evm env t c)
  | Rel _ | Meta _ | Sort _ | Prod _ | Ind _ | Construct _ | Fix _ | CoFix _ | Int _ | Float _ | String _ | Array _ -> None

let cbv_reduce evm env =
  let rec aux c =
    match kind c with
    | Var id -> delta_var_red env id
    | Evar (evi, ev) -> (* Evar solving is not considered progress :( *)
      Evd.existential_opt_value0 evm (evi, ev)
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match aux ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux t)
        (fun _ -> Option.map (fun u -> mkProd (na, t, u)) (aux u))
    | LetIn (na, b, u, c) ->
      Some (
        match aux b with
        | Some b -> mkLetIn (na, b, u, c)
        | None -> subst1 b c
      )
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (aux head)
        ( fun _ ->
          or_step (fun hd -> mkApp (head, array_with args 0 hd)) (aux args.(0))
            ( fun _ ->
              or_else (app_head env head args)
                ( fun _ ->
                  Option.map (fun args -> mkApp (head, args)) (array_step_n aux args 1)
                )
            )
        )
    | Const sp -> const_head env sp
    | Case (ci, u, pms, bi, iv, c, brs) ->
      or_step (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c)
        ( fun _ ->
          or_else (match_head env ci u pms bi iv c brs)
            ( fun _ ->
              or_step (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step aux pms)
                ( fun _ ->
                  match iv with
                  | CaseInvert {indices} -> match_uip_red env ci u pms indices brs
                  | _ -> None
                )
            )
        )
    | Proj (pn, r, c) -> proj_head pn r c
    | Rel _ | Meta _ | Sort _ | Lambda _ | Ind _ | Construct _ | Fix _ | CoFix _ | Int _ | Float _ | String _ | Array _ -> None
  in aux

let cbv_normalize evm =
  let rec aux env c =
    let reduce_or_normalize f c = or_else (cbv_reduce evm env c) (fun _ -> aux (f env) c) in
    match kind c with
    | Evar (evi, ev) ->
      Option.map (fun ev -> mkEvar (evi, ev)) (slist_step (reduce_or_normalize (fun x -> x)) ev)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t)
        (fun _ -> Option.map (fun u -> mkProd (na, t, u)) (aux (push_rel (LocalAssum (na, t)) env) u))
    | Lambda (na, t, c) ->
      or_step (fun c -> mkLambda (na, t, c)) (reduce_or_normalize (push_rel (LocalAssum (na, t))) c)
        ( fun _ ->
          or_step (fun t -> mkLambda (na, t, c)) (reduce_or_normalize (fun x -> x) t)
            (fun _ -> Result.to_option (eta_prime_red evm env t c))
        )
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (aux env head)
        (fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step (aux env) args))
    | Case (ci, u, pms, bi, iv, c, brs) ->
      or_step (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c)
        ( fun _ ->
          or_step (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step (aux env) pms)
            ( fun _ ->
              or_step (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs)) (zeta_match_head env ci u pms brs)
                ( fun _ ->
                  let mind = lookup_mind_specif env ci.ci_ind in
                  let ps = expand_match_param_context mind u pms in
                  or_step (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                    ( for_step
                      ( fun i ->
                        let nas, br = brs.(i) in
                        let ctx = expand_branch_context mind u ps brs i in
                        Option.map (fun br -> array_with brs i (nas, br))
                          (reduce_or_normalize (push_rel_context ctx) br)
                      )
                      (Array.length brs)
                      0
                    )
                    ( fun _ ->
                      let (nas, p), rp = bi in
                      Option.map (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                        ( reduce_or_normalize
                          (push_rel_context (expand_arity_context mind (ci.ci_ind, u) ps nas))
                          p
                        )
                    )
                )
            )
        )
    | Fix (si, (nas, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (nas, tys, bds)))
        (array_step (reduce_or_normalize (push_rec_types (nas, tys, bds))) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (nas, tys, bds)))
            (array_step (reduce_or_normalize (fun x -> x)) tys)
        )
    | CoFix (ri, (nas, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (nas, tys, bds)))
        (array_step (reduce_or_normalize (push_rec_types (nas, tys, bds))) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (nas, tys, bds)))
            (array_step (reduce_or_normalize (fun x -> x)) tys)
        )
    | Proj (pn, r, c) -> Option.map (fun c -> mkProj (pn, r, c)) (aux env c)
    | Array (u, ts, def, ty) ->
      or_step (fun def -> mkArray (u, ts, def, ty)) (reduce_or_normalize (fun x -> x) def)
        ( fun _ ->
          or_step (fun ts -> mkArray (u, ts, def, ty))
            (array_step (reduce_or_normalize (fun x -> x)) ts)
            ( fun _ ->
              Option.map (fun ty -> mkArray (u, ts, def, ty)) (reduce_or_normalize (fun x -> x) ty)
            )
        )
    | Var _ | Rel _ | Meta _ | Sort _ | Cast _ | Const _ | Ind _ | Construct _ | Int _ | Float _ | String _ -> None
    | LetIn _ -> assert false
  in aux

let cbv_step evm env c =
  force "Term is fully reduced." (or_else (cbv_reduce evm env c) (fun _ -> cbv_normalize evm env c))

let global_step evm env c =
  let rec aux env c =
    match kind c with
    | Var id -> delta_var_red env id
    | Evar (evi, ev) ->
      (* Evar solving is not considered progress :( *)
      or_step (fun ev -> mkEvar (evi, ev)) (slist_step (aux env) ev)
        (fun _ -> Evd.existential_opt_value0 evm (evi, ev))
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match aux env ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t)
        (fun _ -> Option.map (fun u -> mkProd (na, t, u)) (aux (push_rel (LocalAssum (na, t)) env) u))
    | Lambda (na, t, c) ->
      or_step (fun c -> mkLambda (na, t, c)) (aux (push_rel (LocalAssum (na, t)) env) c)
        (fun _ ->
          or_step (fun t -> mkLambda (na, t, c)) (aux env t)
            (fun _ -> Result.to_option (eta_prime_red evm env t c))
        )
    | LetIn (na, b, u, c) ->
      Some (
        match aux env b with Some b -> mkLetIn (na, b, u, c)
        | None ->
          match aux (push_rel (LocalDef (na, b, u)) env) c with Some c -> mkLetIn (na, b, u, c)
          | None -> subst1 b c
      )
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (aux env head)
        ( fun _ ->
          or_step (fun hd -> mkApp (head, array_with args 0 hd)) (aux env args.(0))
            ( fun _ ->
              or_else (app_head env head args)
                (fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step_n (aux env) args 1))
            )
        )
    | Const sp -> const_head env sp
    | Case (ci, u, pms, bi, iv, c, brs) ->
      or_step (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c)
        ( fun _ ->
          or_else (match_head env ci u pms bi iv c brs)
            ( fun _ ->
              or_step (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step (aux env) pms)
                ( fun _ ->
                  let mind = lookup_mind_specif env ci.ci_ind in
                  let ps = expand_match_param_context mind u pms in
                  or_else
                    ( match iv with
                      | CaseInvert {indices} -> match_uip_red_specif env mind u ps indices brs
                      | _ -> None
                    )
                    ( fun _ ->
                      or_step
                        (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                        (zeta_match_head env ci u pms brs)
                        ( fun _ ->
                          or_step (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                            ( for_step
                              ( fun i ->
                                let nas, br = brs.(i) in
                                let ctx = expand_branch_context mind u ps brs i in
                                Option.map (fun br -> array_with brs i (nas, br))
                                  (aux (push_rel_context ctx env) br)
                              )
                              (Array.length brs)
                              0
                            )
                            ( fun _ ->
                              let (nas, p), rp = bi in
                              Option.map (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                                ( aux
                                  (push_rel_context (expand_arity_context mind (ci.ci_ind, u) ps nas) env)
                                  p
                                )
                            )
                        )
                    )
                )
            )
        )
    | Fix (si, (nas, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (nas, tys, bds)))
        (array_step (aux (push_rec_types (nas, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (nas, tys, bds)))
            (array_step (aux env) tys)
        )
    | CoFix (ri, (nas, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (nas, tys, bds)))
        (array_step (aux (push_rec_types (nas, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (nas, tys, bds)))
            (array_step (aux env) tys)
        )
    | Proj (pn, r, c) ->
      or_step (fun c -> mkProj (pn, r, c)) (aux env c) (fun _ -> proj_head pn r c)
    | Array (u, ts, def, ty) ->
      or_step (fun def -> mkArray (u, ts, def, ty)) (aux env def)
        ( fun _ ->
          or_step (fun t -> mkArray (u, ts, def, ty)) (array_step (aux env) ts)
            (fun _ -> Option.map (fun ty -> mkArray (u, ts, def, ty)) (aux env ty))
        )
    | Rel _ | Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ | String _ -> None
  in force "Term is fully reduced." (aux env c)

type ('a, 'b, 'c) reduction =
(*| SRRule (* Rewrite rules *)*)
| SRCast of 'c Locus.occurrences_gen (* Cast removal *)
| SRBeta of 'c Locus.occurrences_gen
(* Beta: applied lambda to substitution *)
| SRZeta of 'c Locus.occurrences_gen (* Zeta: letin to substitution *)
| SRZetaMatch of 'a * 'c Locus.occurrences_gen
(* Zetamatch: match-letin to substitution *)
| SRDelta of 'b option * 'c Locus.occurrences_gen
(* Delta: name resolution (including application of primitives) *)
| SREta (* Eta expansion: expand lambda *)
| SREtaPrime of 'c Locus.occurrences_gen
(* Eta reduction:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| SREvar of 'c Locus.occurrences_gen
(* Evar: evar resolution + context substitution, not sure about this one *)
| SRFix of 'c Locus.occurrences_gen
(* Fix: push fixpoint inward when allowed to *)
| SRFixPrime of 'c Locus.occurrences_gen
(* Fixprime: push fixpoint inward, maybe unfold and refold too? *)
| SRCofix of 'c Locus.occurrences_gen (* Cofix: match or project a cofix *)
| SRCofixPrime of 'c Locus.occurrences_gen
(* Cofixprime: push cofix inward, maybe unfold and refold too? *)
| SRMatch of 'c Locus.occurrences_gen
(* Match: match or project on a constructor *)
(* TODO: IOTA (match + fix + cofix)? *)
| SRUIP of 'c Locus.occurrences_gen
(* UIP: inversion of a match with a unique constructor in SProp *)
| SRHead (* Any reduction at head *)
| SRCbv (* Next reduction step of a call-by-value strategy *)
| SRCbn (* Next reduction step of a call-by-name strategy *)
| SRLazy (* Next reduction step of a call-by-need / lazy strategy *)

let map_reduction f g h = function
| SRCast occ -> SRCast (h occ)
| SRBeta occ -> SRBeta (h occ)
| SRZeta occ -> SRZeta (h occ)
| SRZetaMatch (x, occ) -> SRZetaMatch (f x, h occ)
| SRDelta (a, occ) -> SRDelta (Option.map g a, h occ)
| SREta -> SREta
| SREtaPrime occ -> SREtaPrime (h occ)
| SREvar occ -> SREvar (h occ)
| SRFix occ -> SRFix (h occ)
| SRFixPrime occ -> SRFixPrime (h occ)
| SRCofix occ -> SRCofix (h occ)
| SRCofixPrime occ -> SRCofixPrime (h occ)
| SRMatch occ -> SRMatch (h occ)
| SRUIP occ -> SRUIP (h occ)
| (SRHead | SRCbv | SRCbn | SRLazy as s) -> s

let step red env evm c =
  let f =
    match red with
    | SRCast occ -> reduce_with_context occ cast_prep cast_step
    | SRBeta occ -> reduce_with_context occ beta_prep beta_step
    | SRZeta occ -> reduce_with_context occ zeta_prep zeta_step
    | SRZetaMatch ((ind, n, m), occ) ->
      reduce_with_context occ (zeta_match_prep ind n m) (zeta_match_step n m)
    | SRDelta (t, occ) -> reduce_with_context occ (delta_prep t) delta_step
    | SREta -> eta_step evm
    | SREtaPrime occ -> reduce_with_context occ eta_prime_prep (eta_prime_step evm)
    | SREvar occ -> reduce_with_context occ evar_prep (evar_step evm)
    | SRFix occ -> reduce_with_context occ fix_prep fix_step
    | SRFixPrime occ -> reduce_with_context occ fix_prime_prep contract_fix
    | SRCofix occ -> reduce_with_context occ cofix_prep cofix_step
    | SRCofixPrime occ -> reduce_with_context occ cofix_prime_prep contract_cofix
    | SRMatch occ -> reduce_with_context occ match_prep match_step
    | SRUIP occ -> reduce_with_context occ match_uip_prep match_uip_step
    | SRHead -> fun env x -> force "Term at head is not reducible." (head_step evm env x)
    | SRCbv -> cbv_step evm
    | SRCbn -> global_step evm (* LATER *)
    | SRLazy -> global_step evm (* LATER *)
  in
  evm, EConstr.of_constr (f env (EConstr.Unsafe.to_constr c))
