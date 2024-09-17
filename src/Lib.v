From Coq Require Export List.
From Coq Require Export Lia.
From Coq Require Export Compare_dec.
From Coq Require Export Arith.

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
