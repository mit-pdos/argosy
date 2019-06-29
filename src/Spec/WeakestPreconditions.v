Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
Require Import Tactical.ProofAutomation.

Import RelationNotations.

Section Dynamics.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation exec := (exec sem).
  Notation crash_step := sem.(crash_step).
  Notation exec_crash := (exec_crash sem).

  Definition precondition T := forall (post: T -> State -> Prop), State -> Prop.

  Record WPSetup :=
    { op_wp: forall T, Op T -> precondition T;
      op_wp_ok :
        forall T (op:Op T) post s, op_wp op post s ->
                              forall s' v, step op s s' v ->
                                      post v s'; }.

  Ltac cleanup :=
    simpl in *;
    unfold pure, and_then, test, rel_or in *;
    propositional.

  Context (wp: WPSetup).

  Fixpoint precond T (p: proc T)
    : precondition T :=
    fun post =>
      match p with
      | Ret v => post v
      | Do op rx => wp.(op_wp) op (fun v s' => precond (rx v) post s')
      end.

  Theorem wp_ok :
    forall T (p: proc T) (post: T -> State -> Prop),
    forall s, precond p post s ->
         forall s' v, exec p s s' v ->
                 post v s'.
  Proof.
    intros Hop_wp.
    induction p; cleanup; eauto.
    - eapply wp.(op_wp_ok) in H0; eauto.
      eapply H; eauto.
  Qed.

  Definition crashpre := forall (crash: State -> Prop), State -> Prop.
  Definition after_crash (crash: State -> Prop) : State -> Prop :=
    fun s => forall s', crash_step s s' tt -> crash s'.

  Theorem after_crash_unfold : forall crash s,
      after_crash crash s ->
      forall s' u,
        crash_step s s' u ->
        crash s'.
  Proof.
    destruct u; firstorder.
  Qed.

  Ltac after_crash :=
    try match goal with
        | [ H: after_crash ?crash _ |- _ ] =>
          eauto using (@after_crash_unfold crash _ H)
        end.

  Fixpoint crashcond T (p: proc T) : crashpre :=
    fun crash s =>
      match p with
      | Ret v => after_crash crash s
      | Do op rx =>
        after_crash crash s /\
        wp.(op_wp) op (fun v s' => crashcond (rx v) crash s') s
      end.

  Theorem wp_crash_ok T (p: proc T) (crash: State -> Prop) :
    forall s, crashcond p crash s ->
         forall s' v, exec_crash p s s' v ->
                 crash s'.
  Proof.
    induction p; cleanup; after_crash.

    repeat match goal with
           | [ H: _ \/ _ |- _ ] =>
             destruct H; propositional;
            after_crash
           end.

    eapply H; eauto.
    eapply wp.(op_wp_ok) in H2; eauto.
  Qed.

End Dynamics.

Arguments precondition State T : clear implicits.
Arguments crashpre State : clear implicits.
