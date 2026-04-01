From Stdlib Require Extraction.
From Stdlib Require Import ExtrHaskellNatInteger.
From Stdlib Require Import ExtrHaskellBasic.

From RecoveryRefinement Require Import Examples.Logging.Impl.
From RecoveryRefinement Require Import Examples.Logging.ComposedRefinement.

Extraction Language Haskell.

Set Extraction Output Directory "logging-client/extract".

Extract Constant Impl.LogHdr_fmt => "logHdrFmt".
Extract Constant Impl.Descriptor_fmt => "descriptorFmt".

Import LoggingTwoDiskRefinement.
Separate Extraction compile init recover.
