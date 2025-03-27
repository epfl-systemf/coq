(* -*- mode: coq; coq-prog-args: ("-accessible-goal-names") -*- *)

Axiom A : forall (x : nat) P, x = x -> P.

(* eapply *)
Goal 0 = 0.
Proof.
  eapply A.
  [x]: exact 0.
  reflexivity.
Qed.

(* eapply with partial application *)
Goal 0 = 0.
Proof.
  eapply (A _).
  [x]: exact 0.
  reflexivity.
Qed.

(* refine *)
Goal 0 = 0.
Proof.
  refine (A _ _ _).
  [x]: exact 0.
  reflexivity.
Qed.

(* destruct *)
Goal forall A, A \/ A -> A.
Proof.
  intros A H.
  destruct H.
  [or_introl_case]: assumption.
  [or_intror_case]: assumption.
Qed.

(* induction *)
Goal forall x : list nat, x = x.
Proof.
  induction x.
  [nil_case]: reflexivity.
  [cons_case]: reflexivity.
Qed.
