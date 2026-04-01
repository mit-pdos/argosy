From Stdlib Require Export List.
From Stdlib Require Export Lia.
From Stdlib Require Export Compare_dec.
From Stdlib Require Export Arith.

From Classes Require Export Classes.
Require Export Helpers.RelationAlgebra.
Require Export Tactical.ProofAutomation.

Require Export Spec.Proc.
Require Export Spec.ProcTheorems.
Require Export Spec.Hoare.
Require Export Spec.Abstraction.
Require Export Spec.AbstractionSpec.
Require Export Spec.Layer.

Export ProcNotations.

(* require proofs to be strictly bulleted (with only one goal focused at a
time) *)
Global Set Default Goal Selector "!".
