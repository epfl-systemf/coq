(* "Compiler" that builds a lamda term out of a boolean expression [v3] *)
(* the goal is to make a hard to reduce "slowly" mess
   to do that the produced term must be fully reducible with a single reduction rule
   making fixpoints our main enemy:
   they reduce with a fix reduction only if
   the argument which decreases has an exposed constructor
   and they must case on that decreasing argument
   therefore mandatory match which is reduced by a different rule than fix.
   [v1] was the evaluator you expect:
   "eval x := match x with cond c t f => if eval c then eval t else eval f end"
   see the eval without exposed constructor?
   to expose a constructor the match has to be reduced,
   making reduction easy to control by alternating the match and fix rules.
   From there the idea was to build a term in an accumulator.
   [v2] needed a termination proof which doesn't reduce because lemmas are opaque
*)

(* There is an intentional bug somewhere in the evaluation, can you find it? *)

Variant BinOp :=
| BOxor
| BOor
| BOand
| BOimp
.

(* cond c t f is "if c then t else f" *)
Inductive AST :=
| ASTbit : bool -> AST
| ASTnot : AST -> AST
| ASTbop : BinOp -> AST -> AST -> AST
| ASTcond : AST -> AST -> AST -> AST
.

(* to build the expression I first linearize the tree
   otherwise I would need to prove termiation
   which prevents conversion/reduction based evaluation.
   I added reduce markers to tell the second pass to reduce a function
   without relying on a third fixpoint that would be left in the produced value.
*)
Variant LinAST :=
| reduce : LinAST
| Lin_bit : bool -> LinAST
| Lin_not : LinAST
| Lin_bop : BinOp -> LinAST
| Lin_cond : LinAST
.

(* the linear AST is then reduced into partially evaluated functions
   [v2] had those constructors with attached "left to convert" AST nodes
   reducing those nodes would add to the partial value list
   making a termination proof necessary
*)
Variant PartialValue T :=
| v0 : T -> PartialValue T
| v1 : (T -> T) -> PartialValue T
| v2 : (T -> T -> T) -> PartialValue T
| v3 : (T -> T -> T -> T) -> PartialValue T
.

From Stdlib Require Import List.

(* lineraize the tree *)
Fixpoint linearize a s :=
  match a with
  | ASTbit b => Lin_bit b :: s
  | ASTnot a => Lin_not :: linearize a s
  | ASTbop o l r =>
    Lin_bop o :: linearize l (reduce :: linearize r (reduce :: s))
  | ASTcond c t f =>
    Lin_cond
    :: linearize c (reduce :: linearize t (reduce :: linearize f (reduce :: s)))
  end
.

(* Has to use prop to type (x BOOL _ _) with x: BOOL *)
Definition BOOL: Prop := forall T: Prop, T -> T -> T.

(* makes a pure lambda term which fully reduces with beta *)
Fixpoint redBOOL s (v: list (PartialValue BOOL)) :=
  match s with
  | nil =>
    match v with
    | v0 _ b :: nil => Some b
    | _ => None
    end
  | reduce :: s =>
    match v with
    | v0 _ b :: v1 _ g :: v => redBOOL s (v0 BOOL (g b) :: v)
    | v0 _ b :: v2 _ g :: v => redBOOL s (v1 BOOL (g b) :: v)
    | v0 _ b :: v3 _ g :: v => redBOOL s (v2 BOOL (g b) :: v)
    | _ => None
    end
  | Lin_bit true :: s => redBOOL s (v0 BOOL (fun T x y => x) :: v)
  | Lin_bit false :: s => redBOOL s (v0 BOOL (fun T x y => y) :: v)
  | Lin_not :: s =>
    redBOOL s (v1 BOOL (fun x => x _ (fun T x y => y) (fun T x y => x)) :: v)
  | Lin_bop BOxor :: s =>
    redBOOL s (
      v2 BOOL (fun l r => l _ (r BOOL (fun T x y => y) (fun T x y => x)) r) :: v
    )
  | Lin_bop BOor :: s =>
    redBOOL s (v2 BOOL (fun l r => l _ (fun T x y => x) r) :: v)
  | Lin_bop BOand :: s =>
    redBOOL s (v2 BOOL (fun l r => l _ r (fun T x y => y)) :: v)
  | Lin_bop BOimp :: s =>
    redBOOL s (v2 BOOL (fun l r => l _ r (fun T x y => x)) :: v)
  | Lin_cond :: s => redBOOL s (v3 BOOL (fun c t f => c _ t f) :: v)
  end
.

Variant pbool: Prop := ptrue | pfalse.

Definition evalBOOL t :=
  match redBOOL (linearize t nil) nil with
  | None => None
  | Some f => Some (f pbool ptrue pfalse)
  end.

(* this one reduces with match but the match are guarded by beta
   so it is possible to build a non-reduced term,
   then make it fully match reducible at the end by first reducing all beta
*)
Fixpoint red_bool s (v: list (PartialValue bool)) :=
  match s with
  | nil =>
    match v with
    | v0 _ b :: nil => Some b
    | _ => None
    end
  | reduce :: s =>
    match v with
    | v0 _ b :: v1 _ g :: v => red_bool s (v0 bool (g b) :: v)
    | v0 _ b :: v2 _ g :: v => red_bool s (v1 bool (g b) :: v)
    | v0 _ b :: v3 _ g :: v => red_bool s (v2 bool (g b) :: v)
    | _ => None
    end
  | Lin_bit b :: s => red_bool s (v0 bool b :: v)
  | Lin_not :: s =>
    red_bool s (v1 bool (fun x => if x then false else true) :: v)
  | Lin_bop BOxor :: s =>
    red_bool s (
      v2 bool (fun l r => if l then if r then false else true else r) :: v
    )
  | Lin_bop BOor :: s =>
    red_bool s (v2 bool (fun l r => if l then true else r) :: v)
  | Lin_bop BOand :: s =>
    red_bool s (v2 bool (fun l r => if l then r else false) :: v)
  | Lin_bop BOimp :: s =>
    red_bool s (v2 bool (fun l r => if l then r else false) :: v)
  | Lin_cond :: s => red_bool s (v3 bool (fun c t f => if c then t else f) :: v)
  end
.

Definition eval_bool t := red_bool (linearize t nil) nil.

(* Just a container to have the term as a goal *)
Variant Box [T]: T -> Type := box x: Box x.

(* if false & true then true else false *)
Definition test_ast :=
  ASTcond (ASTbop BOand (ASTbit false) (ASTbit true)) (ASTbit true) (ASTbit false).


Goal Box (evalBOOL test_ast).
Proof.
  (* have fun reducing that slowly *)
  unfold evalBOOL.
  cbn fix match delta [linearize test_ast].
  cbn fix match delta [redBOOL].
  cbn beta.
Abort.

Goal Box (eval_bool test_ast).
Proof.
  (* have fun reducing that slowly *)
  unfold eval_bool.
  cbn fix match delta [linearize test_ast].
  cbn fix match delta [red_bool].
  cbn beta.
  cbn match.
Abort.

Definition query x y z :=
  ASTbop BOand
    ( ASTbop BOand
      (ASTbop BOimp (ASTbit x) (ASTbit y))
      (ASTbop BOxor (ASTbit y) (ASTbit z))
    )
    (ASTcond (ASTbit y) (ASTbit z) (ASTbit x)).

Goal forall x y z, eval_bool (query x y z) = Some false.
  intros x y z.
  destruct x, y, z; reflexivity.
Qed.

(* Did you find the bug? *)
