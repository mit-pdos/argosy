From Tactical Require Import Propositional.
From Transitions Require Import Relations Rewriting NonError.

Require Import Spec.Proc.

Import RelationNotations.

Section Abstraction.
  Context (AState CState:Type).
  Context (absr: relation AState CState unit).
  Context (absr_ok:NonError absr).

  Definition refines T
             (p: relation CState CState T)
             (spec: relation AState AState T) :=
    (absr;; p) ---> v <- spec; absr;; pure v.

  Ltac cleanup :=
    repeat match goal with
           | [ x: unit |- _ ] => destruct x
           | [ H: absr _ (Err _ _) |- _ ] =>
             exfalso; eapply absr_ok; eapply H
           | [ H: Val _ _ = Err _ _ |- _ ] =>
             congruence
           | [ H: Val _ _ = Val _ _ |- _ ] =>
             inversion H; subst; clear H
           | _ => eauto 10
           end.

  Ltac split_all :=
    repeat (intuition propositional).

  Theorem refine_unfolded_iff T
          (p: relation CState CState T)
          (spec: relation AState AState T) :
    (forall s s__a, absr s__a (Val s tt) ->
             forall ret, p s ret ->
                    match ret with
                    | Val s' v =>
                      (exists s__a', spec s__a (Val s__a' v) /\
                              absr s__a' (Val s' tt)) \/
                      spec s__a (Err _ _)
                    | Err _ _ => spec s__a (Err _ _)
                    end) <->
    refines p spec.
  Proof.
    unfold refines, rimpl, and_then, pure; split; intros.
    - destruct y; split_all; cleanup.
      specialize (H _ _ ltac:(eauto) _ ltac:(eauto));
        split_all; cleanup.
      specialize (H _ _ ltac:(eauto) _ ltac:(eauto));
        split_all; cleanup.
    - specialize (H s__a ret).
      destruct ret; specialize (H ltac:(eauto));
        split_all; cleanup.
  Qed.

  Theorem refine_unfolded T
          (p: relation CState CState T)
          (spec: relation AState AState T) :
    (forall s s__a, absr s__a (Val s tt) ->
             forall ret, p s ret ->
                    match ret with
                    | Val s' v =>
                      (exists s__a', spec s__a (Val s__a' v) /\
                              absr s__a' (Val s' tt)) \/
                      spec s__a (Err _ _)
                    | Err _ _ => spec s__a (Err _ _)
                    end) ->
    refines p spec.
  Proof. eapply refine_unfolded_iff. Qed.

  Section Dynamics.
    Context C_Op (c_sem: Dynamics C_Op CState).
    Notation c_proc := (proc C_Op).
    Notation c_exec := (exec c_sem).
    Notation c_rexec := (rexec c_sem).

    Definition crash_refines T R
               (p: c_proc T) (rec: c_proc R)
               (exec_spec: relation AState AState T)
               (rexec_spec: relation AState AState R) :=
      refines (c_exec p) exec_spec /\
      refines (c_rexec p rec) rexec_spec.
  End Dynamics.

End Abstraction.

Theorem refines_transitive_abs State1 State2 State3 abs1 abs2 T
        (spec1: relation State1 State1 T)
        (spec2: relation State2 State2 T)
        (spec3: relation State3 State3 T) :
  refines abs1 spec1 spec2 ->
  refines abs2 spec2 spec3 ->
  refines (abs2;; abs1) spec1 spec3.
Proof.
  unfold refines; norm; intros.
  setoid_rewrite H; norm.
  rewrite <- bind_assoc at 1.
  rewrite H0; norm.
Qed.

Theorem refines_respects_bind State1 State2 abs T1 T2
        (r1: relation State1 State1 T1)
        (r2: T1 -> relation State1 State1 T2)
        (r1': relation State2 State2 T1)
        (r2': T1 -> relation State2 State2 T2) :
  refines abs r1 r1' ->
  (forall v, refines abs (r2 v) (r2' v)) ->
  refines abs (and_then r1 r2) (and_then r1' r2').
Proof.
  unfold refines; intros.
  rewrite <- bind_assoc.
  setoid_rewrite H; norm.
  setoid_rewrite H0; norm.
Qed.

Theorem refines_respects_bind_unit State1 State2 abs T2
        (r1: relation State1 State1 unit)
        (r2: unit -> relation State1 State1 T2)
        (r1': relation State2 State2 unit)
        (r2': unit -> relation State2 State2 T2) :
  refines abs r1 r1' ->
  (refines abs (r2 tt) (r2' tt)) ->
  refines abs (and_then r1 r2) (and_then r1' r2').
Proof.
  intros.
  apply refines_respects_bind; auto.
  destruct v; auto.
Qed.

Theorem refines_respects_seq State1 State2 abs T
        (r1 r2: relation State1 State1 T)
        (r1' r2': relation State2 State2 T) :
  refines abs r1 r1' ->
  refines abs r2 r2' ->
  refines abs (r1;; r2) (r1';; r2').
Proof.
  auto using refines_respects_bind.
Qed.

Theorem refines_respects_star State1 State2 abs {abs_ok:NonError abs} T
        (r1: relation State1 State1 T)
        (r2: relation State2 State2 T) :
  refines abs r1 r2 ->
  refines abs (seq_star r1) (seq_star r2).
Proof.
  unfold refines. intros Hr.
  rew simulation_seq_value_no_err; auto.
Qed.

Theorem refines_respects_or State1 State2 abs T
        (r1 r1': relation State1 State1 T)
        (r2 r2': relation State2 State2 T) :
  refines abs r1 r2 ->
  refines abs r1' r2' ->
  refines abs (r1 + r1') (r2 + r2').
Proof.
  unfold refines. intros Hr Hr'.
  repeat rew bind_dist_r.
  repeat rew bind_dist_l.
  rew Hr. rew Hr'.
Qed.
