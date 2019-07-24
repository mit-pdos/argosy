Require Import Spec.Proc.
Require Import Spec.Hoare.

From Transitions Require Import Relations Rewriting NonError.
Require Import Abstraction.
Require Import Layer.

Section Abstraction.
  Context (AState CState:Type).
  Context (absr: relation AState CState unit).
  Context (absr_ok:NonError absr).

  (* define refinement as transforming an abstract specification to a concrete
  one (a program satisfying the abstract spec should satisfy the concrete spec
  after refinement-preserving compilation) *)
  Definition refine_spec T R (spec: Specification T R AState)
    : AState -> Specification T R CState :=
    fun s cs =>
      {| pre := absr s (Val cs tt) /\
                (spec s).(pre);
         post := fun cs' r =>
                   exists s', absr s' (Val cs' tt) /\
                         (spec s).(post) s' r;
         alternate := fun cs' r =>
                        exists s', absr s' (Val cs' tt) /\
                              (spec s).(alternate) s' r; |}.

  Context A_Op C_Op `(a_sem: Dynamics A_Op AState) `(c_sem:Dynamics C_Op CState).

  Import RelationNotations.

  Lemma proc_rspec_refine_exec T R (p: proc C_Op T) (rec: proc C_Op R) spec:
    (forall t, proc_rspec (c_sem) p rec (refine_spec spec t)) ->
    (forall sA sC, absr sA (Val sC tt) -> (spec sA).(pre)) ->
    (_ <- absr; exec (c_sem) p) ---> v <- spec_exec (spec); _ <- absr; pure v.
  Proof.
    intros Hprspec Habstr_pre.
    (*
    intros sA sC b ([]&sTstart&Hrd&Hexec).
    destruct (Hprspec sA).
    eapply H in Hexec. simpl in Hexec.
    clear -Hrd Hexec Habstr_pre.
    edestruct Hexec; eauto. simpl. intuition; eauto.
    do 2 eexists; intuition.
    * intros ?; eauto.
    * firstorder. *)
  Admitted.

  Lemma proc_rspec_refine_rec T R (p: proc C_Op T) (rec: proc C_Op R) spec:
    (forall t, proc_rspec (c_sem) p rec (refine_spec spec t)) ->
    (forall sA sC, absr sA (Val sC tt) -> (spec sA).(pre)) ->
    (_ <- absr; rexec (c_sem) p rec) ---> v <- spec_aexec spec; _ <- absr; pure v.
  Proof.
    intros Hprspec Habstr_pre.
    (*
    intros sA sC b ([]&sTstart&Hrd&Hexec).
    destruct (Hprspec sA).
    eapply H0 in Hexec. simpl in Hexec.
    clear -Hrd Hexec Habstr_pre.
    edestruct Hexec; eauto. simpl. intuition; eauto.
    do 2 eexists; intuition.
    * intros ?; eauto.
    * firstorder. *)
  Admitted.

  Lemma proc_rspec_crash_refines T (p: proc C_Op T) (rec: proc C_Op unit)
        spec op:
    (forall t, proc_rspec c_sem p rec (refine_spec spec t)) ->
    (forall sO sT, absr sO (Val sT tt) -> (spec sO).(pre)) ->
    (spec_exec (spec) ---> exec a_sem (Call op)) ->
    (spec_aexec (spec) --->
                  (a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step)))) ->
    crash_refines absr c_sem p rec (a_sem.(step) op)
                  (a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step))).
  Proof.
    intros ?? He Ha. unfold crash_refines, refines. split.
    - setoid_rewrite <-He. eapply proc_rspec_refine_exec; eauto.
    - setoid_rewrite <-Ha. eapply proc_rspec_refine_rec; eauto.
  Qed.

  (* TODO: think about how to fix this theorem statement for undefined
  behavior *)
  Lemma proc_rspec_crash_refines_op T (p: proc C_Op T) (rec: proc C_Op unit)
        spec (op: A_Op T):
    (forall sA sC, absr sA (Val sC tt) -> proc_rspec c_sem p rec (refine_spec spec sA)) ->
    (forall sA sC, absr sA (Val sC tt) -> (spec sA).(pre)) ->
    (forall sA sC sA' v, absr sA' (Val sC tt) -> (spec sA).(post) sA' v
                         -> (op_spec a_sem op sA).(post) sA' v) ->
    (forall sA sC sA' v, absr sA (Val sC tt) -> (spec sA).(alternate) sA' v
                         -> (op_spec a_sem op sA).(alternate) sA' v) ->
    crash_refines absr c_sem p rec (a_sem.(step) op)
                  (a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step))).
  Proof.
    intros Hprspec Hpre Hpost Halt. unfold crash_refines, refines; split.
    (*
    - setoid_rewrite <-op_spec_complete1.
      unfold spec_exec.
      intros sA sC' t Hl.
      destruct Hl as ([]&sC&?&Hexec).
      eapply (Hprspec sA) in Hexec; eauto.
      simpl in Hexec. edestruct Hexec as (sA'&?&?); eauto.
      { unfold refine_spec; simpl. split; auto. eapply Hpre; eauto. }
      exists t, sA'; split; auto.
      * intros Hpre'. eapply Hpost; eauto.
      * exists tt, sC'; firstorder.
    - setoid_rewrite <-op_spec_complete2.
      unfold spec_aexec.
      intros sA sC' [] Hl.
      destruct Hl as ([]&sC&?&Hexec).
      eapply (Hprspec sA) in Hexec; eauto.
      simpl in Hexec. edestruct Hexec as (sA'&?&?); eauto.
      { unfold refine_spec; simpl. split; auto. eapply Hpre; eauto. }
      exists tt, sA'; split; auto.
      * intros Hpre'. eapply Halt; eauto.
      * exists tt, sC'; firstorder. *)
  Abort.

  Ltac especialize H :=
    match type of H with
     |  forall (_ : ?T), _  =>
        let a := fresh "esp" in
        evar (a: T);
        let a' := eval unfold a in a in
            clear a; specialize (H a')
    end.

  Lemma proc_rspec_recovery_refines_crash_step (rec: proc C_Op unit) spec:
    (forall sA, proc_rspec c_sem rec rec (spec sA)) ->
    (forall sA sC sC', absr sA (Val sC tt) -> crash_step c_sem sC (Val sC' tt) -> (spec sA sC').(pre)) ->
    (forall sA sC sCcrash sC',
        absr sA (Val sC tt) -> crash_step c_sem sC (Val sCcrash tt) ->
        ((spec sA sCcrash).(post) sC' tt \/ (spec sA sCcrash).(alternate) sC' tt) ->
        exists sA', absr sA' (Val sC' tt) /\ crash_step a_sem sA (Val sA' tt)) ->
    refines absr (_ <- c_sem.(crash_step); exec_recover c_sem rec) a_sem.(crash_step).
  Proof.
    intros Hprspec Hpre Hpost_crash. unfold refines.
    (*
    intros sA sC' [] Hl.
    destruct Hl as ([]&sC&Habsr&Hstep).
    destruct Hstep as ([]&sCmid&Hcrash&([]&sCmid'&Hcrash_star&Hrec)).
    edestruct Hprspec as (Hexec&Haexec); eauto.
    unfold rexec in Haexec.
    inversion Hcrash_star; subst.
    - eapply Hexec in Hrec.
      edestruct (Hpost_crash sA sC sCmid' sC') as (sA'&Habsr'&Hcrash'); eauto.
      exists tt, sA'; firstorder.
    - unshelve (especialize (Haexec sCmid sC' tt)).
      { repeat (eexists _, _; split; eauto). }
      edestruct (Hpost_crash sA sC) as (sA'&Habsr'&Hcrash'); eauto.
      exists tt, sA'; firstorder. *)
  Admitted.

  Lemma proc_hspec_init_ok (init: proc C_Op InitStatus) (A_initP: AState -> Prop)
        (C_initP: CState -> Prop) spec:
    proc_hspec c_sem init spec ->
    (forall sC, C_initP sC -> (spec sC).(pre)) ->
    (forall sC sC', (spec sC).(post) sC' Initialized ->
                    exists sA', absr sA' (Val sC' tt) /\ A_initP sA') ->
    (test C_initP;; exec c_sem init)
    ---> (any (T := unit);; test A_initP;; absr;; pure Initialized) +
         (any (T := unit);; pure InitFailed).
  Proof using C_Op c_sem.
    clear a_sem A_Op.
    intros Hproc Hinit_pre Hinit_post.
    (*
    intros sC sC' i ([]&?&(HCinit&<-)&Hexec).
    unfold any, test.
    destruct i.
    - left. edestruct Hinit_post as (sA'&?).
      { eapply Hproc; eauto. }
      do 2 (exists tt, sA'; split; intuition). firstorder.
    - right. exists tt, sC';  do 2 eexists; intuition. *)
  Admitted.

End Abstraction.
