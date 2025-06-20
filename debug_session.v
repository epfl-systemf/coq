Import Nat.
Definition option_bind [T U] o (f: T -> option U) :=
  match o with
  | Some x => f x
  | None => None
  end.

Notation "'Let' x ':=' y 'in' z" :=
  (option_bind y (fun x => z)) (x ident, at level 200).




Inductive PureLambda :=
| var : nat -> PureLambda
| lambda : PureLambda -> PureLambda
| appl : PureLambda -> PureLambda -> PureLambda
.

Fixpoint lift k t :=
  match t with
  | var n => var (k + n)
  | lambda t => lambda (lift k t)
  | appl t u => appl (lift k t) (lift k u)
  end.

Fixpoint replace x k t :=
  match t with
  | var n => if n =? k then var n else lift k x
  | lambda t => lambda (replace x (k + 1) t)
  | appl t u => appl (replace x k t) (replace x k u)
  end.

(* reduce until no more visible or immediately created redexes *)
Fixpoint reduce_redexes_bottom_up t :=
  match t with
  | var n => var n
  | lambda t => lambda (reduce_redexes_bottom_up t)
  | appl (lambda t) x =>
    replace
      (reduce_redexes_bottom_up x)
      O
      (reduce_redexes_bottom_up t)
  | appl t x =>
    let x := reduce_redexes_bottom_up x in
    match reduce_redexes_bottom_up t with
    | lambda t => replace x O t
    | t => appl t x
    end
  end.

Fixpoint unlift t :=
  match t with
  | var O => None
  | var (S n) => Some (var n)
  | lambda t => option_map lambda (unlift t)
  | appl t u =>
    Let t := unlift t in
    option_map (appl t) (unlift u)
  end.

Fixpoint ensure_normal_form k t :=
  match t with
  | var n =>
    if n <? k
    then Some (var n)
    else None (* open term *)
  | lambda t =>
      Let t := ensure_normal_form (k + 1) t in
      let t :=
        match t with
        | appl t' (var O) =>
          match unlift t' with
          | Some t => t (* eta reduce *)
          | None => t
          end
        | _ => t
        end
      in Some (lambda t)
  | appl t x =>
    Let t := ensure_normal_form k t in
    match t with
    | lambda _ => None (* visible redex *)
    | _ => option_map (appl t) (ensure_normal_form k x)
    end
  end.

(* eval_with_fuel, repeat bottom-up redexes *)
Fixpoint eval_with_fuel n t :=
  match n with
  | O => ensure_normal_form O t
  | S n => eval_with_fuel n (reduce_redexes_bottom_up t)
  end.

(* \f\x f x *)
Definition one := lambda (lambda (appl (var 1) (var 0))).
(* \f\x f (f x) *)
Definition two :=
  lambda (lambda (appl (var 1) (appl (var 1) (var 0)))).
(* \n\m\f\x (n f) (m f x) *)
Definition plus :=
  lambda (lambda (lambda (lambda (
    appl (appl (var 3) (var 1))
      (appl (appl (var 2) (var 1)) (var 0))
   ))))
.
Definition one_plus_one := appl (appl plus one) one.

Eval vm_compute in eval_with_fuel 2 one_plus_one.
Fail Timeout 5
  Eval vm_compute in eval_with_fuel 3 one_plus_one.
(* = None
 "call_of_nature 3 one_plus_one" takes forever
*)

Goal eval_with_fuel 2 one_plus_one = Some two.
  (* Your job is to debug, glhf *)


  (* delta reduction on eval_with_fuel? *)































  unfold eval_with_fuel.
  Print eval_with_fuel.
  Undo.



































  cbv delta [eval_with_fuel]. Undo.









  unfold eval_with_fuel.
  (* After reading the documentation of cbn and simpl,
     you can do the following
  *)
  simpl reduce_redexes_bottom_up.
  do 3 (cbn fix delta [ensure_normal_form]; cbn match; cbn [add]).
  (* reduce first ensure normal form *)
  Ltac step_in target :=
    (cbn fix delta [ensure_normal_form] in target; cbn match in target; cbn [add] in target).
  set (e0 := ensure_normal_form 2 _).
  do 3 step_in e0.
  set (e1 := ensure_normal_form 4 _) in e0.
  step_in e1.
  set (e2 := ensure_normal_form 4 _) in e1.
  do 3 step_in e2.
  set (e3 := ensure_normal_form 6 _) in e2.
  do 3 step_in e3.
  step_in e3.
  cbn [ltb leb option_bind] in e3.
  (* who can tell me why it appeared? *)







  
Abort.

Goal eval_with_fuel 2 one_plus_one = Some two.
  (* You read more documentation (change, cbv)
     and you know better how to approach the problem
  *)
  unfold eval_with_fuel.
  cbn [reduce_redexes_bottom_up one_plus_one].
  change (reduce_redexes_bottom_up one) with one.
  change (reduce_redexes_bottom_up plus) with plus.
    unfold plus at 1.
  (* Huh, did we go too far?
     replace one 0
      (reduce_redexes_bottom_up
         (lambda
            (lambda
              (lambda
                (appl
                  (appl (var 3) (var 1))
                  (appl (appl (var 2) (var 1)) (var 0)))))))
  *)
    Undo.
  set (e := match plus with lambda t => _ | _ => _ end) at 1.
  cbv delta [plus] in e.
  cbv match in e.
  (* Turns out we did not go too far *)
  cbn [reduce_redexes_bottom_up] in e.
  subst e.
    cbn [replace]. Undo.
    unfold replace at 1. Undo.
  cbn delta [replace].
  set (e := replace _ _ _).
  cbn -[one] in e.
  subst e.
  Fail change (lift 3 one) with one.
Abort.

Goal eval_with_fuel 2 one_plus_one = Some two.
  step delta eval_with_fuel. Undo.
  unfold eval_with_fuel.
  step delta one_plus_one.
  set (one1 := one) at 1.
  set (one2 := one).
  step delta ensure_normal_form. Undo.
  step delta reduce_redexes_bottom_up at 2.
  step fix.
  fold reduce_redexes_bottom_up.
  step beta.
  cbv match. Undo. (* INTEREST EVEN IN SIMPLE CASES *)
  step match.
  do 2 step beta.
  change (reduce_redexes_bottom_up one2) with one2.
  step zeta.
  step match.
  do 2 step beta.
  step delta reduce_redexes_bottom_up at 2.
  step fix.
  fold reduce_redexes_bottom_up.
  step beta.
  step match.
  step beta.
  step beta.
  change (reduce_redexes_bottom_up one1) with one1.
  step zeta.
  step delta plus at 1.
  step match.
  step beta.
  step delta reduce_redexes_bottom_up at 2.
  step fix.
  fold reduce_redexes_bottom_up.
  step beta.
  step match.
  step beta.
  step delta replace at 1.
  step fix.
  fold replace.
  do 3 step beta.
  step match.
  change (0 + 1) with 1.
  step beta.
  step match.
  step beta.
  change (reduce_redexes_bottom_up ?x) with x at 2.
  step delta replace at 2.
  step fix.
  fold replace.
  do 3 step beta.
  step match.
  step beta.
  change (1 + 1) with 2.
  step delta replace at 2.
  step fix.
  fold replace.
  do 3 step beta.
  step match.
  step beta.
  change (2 + 1) with 3.
  step delta replace at 2.
  step fix.
  fold replace.
  do 3 step beta.
  step match.
  do 2 step beta.
  step delta replace at 2.
  step fix.
  fold replace.
  do 3 step beta.
  step match.
  do 2 step beta.
  Fail change (replace one1 3 (var 3)) with one1. (* HUH *)
  Fail change (replace one1 3 (var 1)) with (var 1). (* HUH *)
  step delta replace at 2.
  step fix.
  fold replace.
  do 3 step beta.
  step match.
  step beta. (* FOUND THE FIRST STUPID MISTAKE *)
  Undo 6.
  set (
    fix replace_fix1 x k t :=
      match t with
      | var n => if n =? k then lift k x else var n
      | lambda t => lambda (replace_fix1 x (k + 1) t)
      | appl t u =>
        appl (replace_fix1 x k t) (replace_fix1 x k u)
      end
  ) as replace_fix1.
  change_no_check replace with replace_fix1.
  change (replace_fix1 _ _ (var 1)) with (var 1).
  Fail change (replace_fix1 one1 3 (var 3)) with one1.
  (* HUH *)
  step delta replace_fix1 at 2.
  step fix.
  fold replace_fix1.
  do 3 step beta.
  step match.
  step beta.
  change (3 =? 3) with true.
  step match.
  step delta lift.
  Fail step fix. (* SHOW THIS *)
  step fix'.
  fold lift.
  do 2 step beta. (* FOUND THE SECOND STUPID MISTAKE *)
  Undo 5.
  set (
    fix lift_fix1 k m t :=
      match t with
      | var n => if m <=? n then var (k + n) else var n
      | lambda t => lambda (lift_fix1 k (m + 1) t)
      | appl t u => appl (lift_fix1 k m t) (lift_fix1 k m u)
      end
  ) as lift_fix1.
  change_no_check (lift ?x) with (lift_fix1 x 0) in *.
  change (lift_fix1 _ _ one1) with one1.
  change (replace_fix1 one1 _ ?x) with x.
  cbn [replace_fix1 add eqb].
  change (replace_fix1 _ _ one1) with one1.
  change (lift_fix1 _ _ one2) with one2.
Abort.

Fixpoint lift_fix k m t :=
  match t with
  | var n => if m <=? n then var (k + n) else var n
  | lambda t => lambda (lift_fix k (m + 1) t)
  | appl t u => appl (lift_fix k m t) (lift_fix k m u)
  end.

Fixpoint replace_fix1 x k t :=
  match t with
  | var n => if n =? k then lift_fix k 0 x else var n
  | lambda t => lambda (replace_fix1 x (k + 1) t)
  | appl t u => appl (replace_fix1 x k t) (replace_fix1 x k u)
  end.

Fixpoint reduce_redexes_bottom_up_depfix1 t :=
  match t with
  | var n => var n
  | lambda t => lambda (reduce_redexes_bottom_up_depfix1 t)
  | appl (lambda t) x =>
    replace_fix1
      (reduce_redexes_bottom_up_depfix1 x)
      O
      (reduce_redexes_bottom_up_depfix1 t)
  | appl t x =>
    let x := reduce_redexes_bottom_up_depfix1 x in
    match reduce_redexes_bottom_up_depfix1 t with
    | lambda t => replace_fix1 x O t
    | t => appl t x
    end
  end.

Fixpoint eval_with_fuel_depfix1 n t :=
  match n with
  | O => ensure_normal_form O t
  | S n =>
    eval_with_fuel_depfix1
      n
      (reduce_redexes_bottom_up_depfix1 t)
  end.

Eval vm_compute in eval_with_fuel_depfix1 100 one_plus_one.
(* = None
   Surely this was enough fuel
*)

Goal eval_with_fuel_depfix1 2 one_plus_one = Some two.
  unfold eval_with_fuel_depfix1.
  simpl reduce_redexes_bottom_up_depfix1 at 2.
  fold one.
  (* Old state *)
  step delta reduce_redexes_bottom_up_depfix1.
  step fix.
  fold reduce_redexes_bottom_up_depfix1.
  step beta.
  step match.
  step beta.
  step delta reduce_redexes_bottom_up_depfix1.
  step fix.
  fold reduce_redexes_bottom_up_depfix1.
  step beta.
  step match.
  step beta.
  step delta reduce_redexes_bottom_up_depfix1.
  step fix.
  fold reduce_redexes_bottom_up_depfix1.
  step beta.
  step match.
  do 2 step beta.
  step match.
  do 2 step beta.
  step delta reduce_redexes_bottom_up_depfix1 at 1.
  step fix.
  fold reduce_redexes_bottom_up_depfix1.
  step beta.
  step match.
  do 2 step beta.
  step match.
  do 2 step beta.
  change (reduce_redexes_bottom_up_depfix1 (var 0))
    with (var 0).
  step zeta at 2.
  set (e := reduce_redexes_bottom_up_depfix1 _).
  step delta reduce_redexes_bottom_up_depfix1 in e.
  step fix in e.
  fold reduce_redexes_bottom_up_depfix1 in e.
  step beta in e.
  step match in e.
  do 2 step beta in e.
  step delta one in (value of e) at 1.
  step match in e.
  step beta in e.
  change (reduce_redexes_bottom_up_depfix1 (var 1))
    with (var 1) in e.
  change (reduce_redexes_bottom_up_depfix1 ?x) with x in e.
  change (lambda (appl (var 2) (var 0))) in (value of e).
  subst e.
  step match.
  step beta.
  Fail change (replace_fix1 ?x 0 (appl (var 2) (var 0)))
    with (appl (var 1) x).
  (* HUH *)
  step delta replace_fix1 at 2.
  step fix.
  fold replace_fix1.
  do 3 step beta.
  step match.
  do 2 step beta.
  change (replace_fix1 ?x 0 (var 0)) with x.
  Fail change (replace_fix1 _ 0 (var 2)) with (var 1).
  (* HUH *)
  step delta replace_fix1 at 2.
  step fix.
  fold replace_fix1.
  do 3 step beta. (* FOUND THE MISTAKE *)
  Undo 12.
  set (
    fix replace_fix2 x k t :=
      match t with
      | var n =>
        match compare n k with
        | Eq => lift k x 
        | Lt => var n
        | Gt => var (n - 1)
        end
      | lambda t => lambda (replace_fix2 x (k + 1) t)
      | appl t u =>
        appl (replace_fix2 x k t) (replace_fix2 x k u)
      end
  ) as replace_fix2.
  change_no_check replace_fix1 with replace_fix2.
  change (replace_fix2 ?x 0 (appl (var 2) (var 0)))
    with (appl (var 1) x).
  step zeta.
  vm_compute. (* WE'RE DONE *)
Abort.

Variant reduction :=
| Beta: reduction
| Zeta: reduction
| Delta: reduction
| Fix: reduction
| Cofix: reduction
| Match: reduction
| Head: reduction
.

Tactic Notation "red_at" constr(ured) open_constr(p) :=
  match goal with
  | [ |- context C[p as tm] ] =>
    let tm0 :=
      match ured with
      | Beta => eval cbv beta in tm
      | Zeta => eval cbv zeta in tm
      | Delta => eval cbv delta in tm
      | Fix => eval cbv fix in tm
      | Cofix => eval cbv cofix in tm
      | Match => eval cbv match in tm
      | Head => eval red in tm
      end
    in
    let tm1 := context C[tm0] in
    change tm1
  end.

Ltac red_aux check n :=
  match goal with
  | [ |- ?g ] =>
    tryif check g
    then idtac "Found match after" n "steps"
    else
      first
        [ step cbv; try red_aux check (S n)
        | idtac "Fully reduced after" n "steps"
        ]
  end.

Ltac red_until check := red_aux check 0.

Goal eval_with_fuel 2 one_plus_one = Some two.
  (* red_until
       ltac:(fun g =>
         match g with
         | context [match None with _ => _ end] => idtac
         end).
     Found match after 12054 steps
     what are we comparing?
  *)

  Time do 11800 step cbv.
  red_until
    ltac:(fun g =>
      match g with
      | context [S _ <? _] => idtac
      end).
  (* Found match after 186 steps *)
  (* This is probably possible,
     but step cbv is not the right candidate for that:
     the order of operations is suboptimal
  *)
Abort.
