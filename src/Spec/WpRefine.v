From Tactical Require Import Propositional.

From Transitions Require Import Relations.

Require Import Spec.Proc.
(*
Require Import Spec.WeakestPreconditions.

Section Dynamics.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation exec := (exec sem).

  Context AState (absr: relation AState State unit).
  Context (wp: WPSetup sem).

  Theorem wp_refine T (p: proc T) (r: relation AState AState T) :
    (forall s s__a, absr s__a s tt ->
             precond wp p (fun v s' =>
                             exists s__a', r s__a s__a' v /\
                                    absr s__a' s' tt) s) ->
    refines absr (exec p) r.
  Proof.
    intros.
    eapply refine_unfolded; intros.
    eapply H in H0; eauto.
    eapply wp_ok in H0; eauto.
  Qed.
End Dynamics.
*)
