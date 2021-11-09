From RecoveryRefinement Require Import Lib.
Require Export Maybe.
Require Export Disk.
Require Import TwoDiskAPI.

Import RelationNotations.
Import TwoDisk.
Import Helpers.RelationAlgebra.
Import RelationNotations.

Section specs.

  (** Simple wrapper specs that just capture the exact semantics of the operations.
     We use these exclusively in this file to prove higher level specs below. *)
  Lemma read_op_ok :
    forall i a,
      proc_hspec TDBaseDynamics (td.read i a) (op_spec TDBaseDynamics (op_read i a)).
  Proof. intros. eapply op_spec_sound. Qed.

  Lemma write_op_ok :
    forall i a b,
      proc_hspec TDBaseDynamics (td.write i a b) (op_spec TDBaseDynamics (op_write i a b)).
  Proof. intros. eapply op_spec_sound. Qed.

  Lemma size_op_ok :
    forall i,
      proc_hspec TDBaseDynamics (td.size i) (op_spec TDBaseDynamics (op_size i)).
  Proof. intros. eapply op_spec_sound. Qed.

  Hint Resolve read_op_ok : core.
  Hint Resolve write_op_ok : core.
  Hint Resolve size_op_ok : core.


  (** We now define easier-to-use specifications written in terms of
  [maybe_holds] (the ?|= notation) for the TwoDisk layer.  The fact that at least
  one disk is always functioning is encoded in the inductive type
  [TwoDiskBaseAPI.State] itself; it has only three cases, for both disks, only
  disk 0, and only disk 1.  *)


  Definition other (i : diskId) :=
    match i with
    | d0 => d1
    | d1 => d0
    end.

  Definition read_spec (i : diskId) (a : addr) : _ -> Specification _ (unit) State :=
    fun '(d, F) state => {|
      pre :=
        get_disk i         state ?|= eq d /\
        get_disk (other i) state ?|= F;
      post := fun state' r =>
        match r with
        | Working v =>
          get_disk i         state' ?|= eq d /\
          get_disk (other i) state' ?|= F /\
          index d a ?|= eq v
        | Failed =>
          get_disk i         state' ?|= missing /\
          get_disk (other i) state' ?|= F
        end;
      alternate := fun state' r =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F;
    |}.

  Definition write_spec (i : diskId) (a : addr) (b : block)
    : _ -> Specification (DiskResult unit) unit _ :=
    fun '(d, F) state => {|
      pre :=
        get_disk i         state ?|= eq d /\
        get_disk (other i) state ?|= F;
      post := fun state' r =>
        match r with
        | Working _ =>
          get_disk i         state' ?|= eq (assign d a b) /\
          get_disk (other i) state' ?|= F
        | Failed =>
          get_disk i         state' ?|= missing /\
          get_disk (other i) state' ?|= F
        end;
      alternate := fun state' _ =>
        (get_disk i state' ?|= eq d \/
         get_disk i state' ?|= eq (assign d a b) /\ a < length d) /\
        get_disk (other i) state' ?|= F;
    |}.

  Definition size_spec (i : diskId) : _ -> Specification _ unit _ :=
    fun '(d, F) state => {|
      pre :=
        get_disk i         state ?|= eq d /\
        get_disk (other i) state ?|= F;
      post := fun state' r =>
        match r with
        | Working n =>
          get_disk i         state' ?|= eq d /\
          get_disk (other i) state' ?|= F /\
          n = length d
        | Failed =>
          get_disk i         state' ?|= missing /\
          get_disk (other i) state' ?|= F
        end;
      alternate := fun state' _ =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F;
    |}.

    Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: bg_failure _ _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem maybe_holds_stable : forall state state' F0 F1 i,
    get_disk (other i) state ?|= F0 ->
    get_disk i state ?|= F1 ->
    bg_failure state state' tt ->
    get_disk (other i) state' ?|= F0 /\
    get_disk i state' ?|= F1.
  Proof.
    intros.
    destruct i; inv_bg; simpl in *; eauto.
  Qed.

  Lemma identity_unfold S (s s': S) T (v: T) :
      identity s s' v ->
      s' = s.
  Proof.
    unfold identity; auto.
  Qed.

  Ltac cleanup :=
    repeat match goal with
           | [ |- forall _, _ ] => intros
           | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
           | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
           | [ H: identity _ _ _ |- _ ] => apply identity_unfold in H
           | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
           | [ H: bg_failure _ _ _ |- _ ] =>
             eapply maybe_holds_stable in H;
             [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
           | [ H: _ ?|= eq _, H': _ = Some _ |- _ ] =>
                    pose proof (holds_some_inv_eq _ H' H); clear H
           | [ H: ?A * ?B |- _ ] => destruct H
           | [ H: DiskResult _ |- _ ] => destruct H
           | _ => deex
           | _ => destruct_tuple
           | _ => progress autounfold in *
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress safe_intuition
           | _ => solve [ eauto ]
           | _ => congruence
           | _ => inv_step
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr eqn:?; [ | solve [ repeat cleanup ] ]
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr eqn:?; [ solve [ repeat cleanup ] | ]
           end.

  Ltac prim :=
    intros;
    eapply proc_hspec_impl; [ unfold spec_impl | eauto ]; eexists;
    intuition eauto; cleanup;
    intuition eauto; cleanup.

  Hint Resolve holds_in_some_eq : core.
  Hint Resolve holds_in_none_eq : core.
  Hint Resolve pred_missing : core.

  Hint Resolve tt : core.


  Theorem read_ok : forall i a dF, proc_hspec TDBaseDynamics (td.read i a) (read_spec i a dF).
  Proof.
    unshelve prim; eauto.
  Qed.

  Ltac destruct_all :=
    repeat match goal with
           | _ => solve [ auto ]
           | [ i: diskId |- _ ] => destruct i
           | [ |- context[match ?s with
                         | BothDisks _ _ => _
                         | OnlyDisk0 _ => _
                         | OnlyDisk1 _ => _
                         end] ] => destruct s
           | _ => simpl in *
           end.


  Theorem write_ok : forall i a v dF, proc_hspec TDBaseDynamics (td.write i a v) (write_spec i a v dF).
  Proof.
    unshelve prim; eauto;
      try solve [ destruct_all ].
    try rename d0 into d2. (* compat: variable is named d2 in coq < 8.15 but d0 in coq >= 8.15 *)
    destruct (le_dec (S a) (length d2)).
    destruct_all.
    autorewrite with array.
    destruct_all.
  Qed.

  Theorem size_ok : forall i dF, proc_hspec TDBaseDynamics (td.size i) (size_spec i dF).
  Proof.
    unshelve prim.
  Qed.
End specs.

Global Hint Resolve write_ok size_ok read_ok : core.
