---
title: "Argosy: Verifying layered storage systems with recovery refinement"
---

[![Build Status](https://travis-ci.org/mit-pdos/argosy.svg?branch=master)](https://travis-ci.org/mit-pdos/argosy)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

The code is licensed under the MIT license.

This artifact is licensed under the Creative Commons Attribution license.

# Getting started

## Installing dependencies

There are three ways to build Argosy:

- Compile from this source distribution
- Compile from a tag in the git repo
- Compile within a provided Xubuntu virtual machine with dependencies pre-installed

To compile from source, you'll need Coq (v8.8.2, v8.9, or master) to compile the
main development and Haskell stack to build and run the logging and replicated
disk example. You'll also need `make`. We have no external Coq dependencies
(dependencies are included as git submodules and use a fixed commit hash) and
stack provides reproducible, sandboxed builds for the Haskell dependencies.

If you use macOS, you can install these dependencies with `brew install coq
haskell-stack`. If you use Arch Linux you can use `sudo pacman -S coq
haskell-stack`.

The Ubuntu versions of both of these dependencies are too old, so you'll need to
install them manually. The easiest way to install Coq is [through
opam](https://coq.inria.fr/opam-using.html). The easiest way to install stack is
with their installer (`wget -qO- https://get.haskellstack.org/ | sh`).

### Building from source

If you want to compile from the repo instead of this packaged release, you can
clone it from [github.com/mit-pdos/argosy](https://github.com/mit-pdos/argosy),
keeping in mind to get the submodules:

```
git clone -b v0.1.0 --recurse-submodules https://github.com/mit-pdos/argosy
```

Our code is open source; please feel free to share anything in this artifact or
the codebase (although please point people to GitHub rather than this static
artifact).

### Downloading the VM

We also have a VirtualBox VM available at
<https://www.dropbox.com/s/3p70ee0azbgs7lm/argosy-vm.ova?dl=1>. The VM image is
2GB.

The default settings are 4GB of RAM and 2 vCPUs, but Argosy builds in a couple
minutes with as little as 1GB of RAM and 1 vCPU. The VM's default user has no
password and sudo access. A copy of the artifact is in the home folder at
`~ubuntu/argosy-artifact`.

## Compiling

Running `make` within the source will compile the proofs and print two things: the type of the
main correctness theorem, applied to the composed logging and replication
system, and a list of assumptions. These assumptions are:

- `eq_rect_eq`, a standard assumption about dependent equality.
- The three axioms `bytes`, `bytes0`, and `bytes_dec`, which form a model of
  byte sequences and are instantiated with Haskell's `Data.ByteString` in the
  extracted code.
- `Impl.LogHdr_fmt` and `Impl.Descriptor_fmt`, axiomatic code to encode the
  logging data structures.

The whole development should compile in under two minutes and within one GB of
RAM (and under a minute with `make -j2`).

To compile the logging code, run its unit tests, and see a demo of using
logging-client, after compiling the Coq code (which also runs extraction), run:

```
cd logging-client
stack test
./demo.sh
```

# Connections between paper and code

We refer to identifiers by their qualified Coq name; to find `Spec.Proc.proc`
you'd look in `Spec/Proc.v` for a definition called `proc`.

## Section 2 (encoding the semantics)

- An **abstraction layer $L$ (L205)** corresponds to the type
  `Spec.Layer.Layer`. The type is indexed by a type constructor `Op : Type ->
  Type` for operations, written $O$ in the paper.
- **$\operatorname{Proc}_L$ (L259)** is indexed by a layer. The codebase has `Spec.Proc.proc`
  indexed by just `Op : Type -> Type` (the other components of layers do not
  influence syntax, only semantics).
- **$\operatorname{Rel}(A, B, T)$** (L299) and its associated definitions are in
  `Helpers.RelationAlgebra`. The theorems listed in **Figure 3 (L338)** are also
  in this file (eg, `and_then_monotonic`, `seq_sliding`, `denesting`, and
  `simulation_seq`).
- The **dynamics of programs** defined by $\operatorname{exec(e)}$,
  $\operatorname{execHalt}(e)$, and $\operatorname{rexec}(e, r)$, correspond to
  `Spec.Proc`.

## Section 3 (metatheory)

- **Definition 2, recovery refinement (L481)** correspond to
  `Spec.Layer.LayerRefinement`. Implementations $I$ are of type
  `Spec.Layer.LayerImpl`, which is indexed by the two operation type
  constructors. Refinements are indexed by both layers (the section variables
  `c_layer` and `a_layer`).
- **Theorem 3 (L539) and Theorem 4 (L563)** are crucial lemmas relating compiled
  and abstract executions. They correspond to the theorems
  `Spec.Layer.compile_exec_ok` and `Spec.Layer.compile_rexec_ok`. The former's
  proof is mostly equational reasoning so it largely consists of the relation
  algebra tactics `norm`, and `rew` (which wraps `rewrite` and `setoid_rewrite`
  for rewriting by relational (in)equalities). The latter proof is also largely
  Kleene algebra inequational reasoning (some of which is in `rexec_star_rec`).
  The equality shown in L572-577 is `Spec.ProcTheorems.exec_recover_bind`.
- **Theorem 5, Correctness for sequences (L650)**, the main correctness theorem
  for a layer implementation, corresponds to
  `Spec.Layer.complete_exec_seq_ok_unfolded`. There are several variants above
  this definition, but this theorem's statement is the easiest to understand
  since it refers to more basic definitions.
- **Theorem 6, Composition (L677)**, the theorem that makes layer proofs
  modular, corresponds to `Spec.Layer.refinement_transitive`. The theorem as
  stated in Coq is _computationally relevant_; that is, the produced refinement
  has the composed implementation inside it (built using `layer_impl_compose`)
  as well as proofs for all the recovery refinement obligations. Because we want
  to run this implementation the proof ends with `Defined` instead of `Qed`.

## Section 4 (Crash Hoare Logic)

- The **recovery quadruple (L733)** and **halt specification (L754)** correspond
  to `Spec.Hoare`'s `proc_rspec` and `proc_hspec`, respectively. The type of
  specifications is common to these and uses the term "alternate" for the halt
  or recovery condition, depending on context.
- While unfortunately not described in the paper, CHL specs connect to recovery
  refinement via a set of definitions and theorems in `Spec.AbstractionSpec`.
  First, the definition `refine_spec` captures a pattern of writing specs at a
  higher layer of abstraction using an abstraction relation in the pre-, post-,
  and recovery/halt condition. Second, the file has a number of generic theorems
  that connect Hoare specs to refinement. This connection is a bit messy
  (there's some boilerplate when proving a refinement property from specs, as
  seen in `Examples.ReplicatedDisk.ReplicatedDiskImpl.compile_refine_TD_OD`, for
  example).
- The **idempotence-ghost rule (L811)** corresponds to
  `Spec.Hoare.proc_hspec_to_rspec` (we don't prove the weaker idempotence
  principle from FSCQ's CHL).
- One of the more interesting parts of **Figure 6 (L890)** is the sequencing
  rule for halt specs; this corresponds to `Spec.Hoare.proc_hspec_rx`. Weakening
  corresponds to `Spec.Hoare.proc_hspec_impl` (though most of the theorem
  statement is in the `spec_impl` definition).

## Section 5 (Examples)

For a simple illustration of the framework, we recommend reading
`Examples/StatDb/Impl.v` followed by `Examples.StatDb/HoareProof.v`. The
abstract layer as two operations: `add(n:nat)` to store in the database and
`avg() : Op nat` to get the average of the numbers added so far. These two
operations are implemented using two variables, one for the number of elements
and the other for the running sum. The database is cleared on a crash, so there
is no crash or recovery reasoning, and there is only a single layer, but the
example illustrates writing layer definitions, CHL specs, and proving refinement
all the same.

The more complete examples in the paper are in `Examples/ReplicatedDisk/` and
`Examples/Logging/`. The two layers are composed together as described in
**Figure 10 (L1111)** in `Examples.Logging.ComposedRefinement`, which simply
applies `refinement_transitive` to the two layer implementations.

The logging layer relies on unverified encoders for converting the logging data
structures to and from blocks. These axioms are then replaced by Haskell
implementations during extraction, and those implementations have QuickCheck
tests for the properties we assume in Coq (see
`logging-client/test/LogEncodingSpec.hs` and compare to the correctness property
in `Examples.Logging.LogEncoding.block_encoder`). We do use nats for simplicity
in the Coq representation, so these encoders will fail at runtime if disk
addresses overflow a 64-bit integer.

## Section 6

The script that produces the lines of code table at L1177 is provided in the
artifact; run `loc.sh <path to argosy src>` to reproduce these numbers (you'll
need cloc and sqlite3 for this script). The LaTeX table was manually constructed
from the output, which includes more details for debugging.

# Source code overview

The `src` subdirectory contains the Coq development. Within that directory:

* The folder `Helpers` contains various useful libraries:

    * `Disk.v` -- a model of disks as lists of blocks.
      Blocks themselves are treated as an abstract type, with a few properties
      axiomatized -- during extraction, they are mapped to Haskell ByteStrings.

    * `RelationAlgebra.v` -- defines relational
      combinators and proves their basic properties.

    * `RelationRewriting.v` -- provides tactics
      to normalize and rewrite by equational/inequational laws for relations.

* The folder `Spec` contains files for the semantics of programs and
  reasoning about them.

    * `Proc.v` -- definition of the syntax and semantics of
      programs as free monads generated by set of basic operations.

    * `Layer.v` -- defines layers, which define an "API" as a
      bundle of operations and a form of state. Also describes how to implement a
      layer in terms of another, compilation between layers, and the notion of
      layer refinement (which we also call "recovery refinement"). The theorem
      `compile_exec_seq_ok` proves that layer refinements preserve the semantics
      of complete interactions. `refinement_transitive` composes two
      implementations and shows the composition is also a recovery refinement.

    * `Hoare.v` -- our embedding of Crash Hoare Logic (CHL),
      which we use to help prove that an implementation is a layer refinement.

* The folder `Examples` contains examples of using the framework to prove
  recovery refinement.

    * `ReplicatedDisk` -- contains an example
      proving that a disk replication implementation is a recovery refinement
      from a layer with a single robust disk, into a layer with two faulty
      disks. `OneDiskAPI.v` and
      `TwoDiskAPI.v` define the source
      and target layers, while
      `ReplicatedDiskImpl.v`
      is the implementation and proof that it is a refinement.

    * `Logging` -- contains an example proving that a
      write-ahead logging implementation is a recovery refinement from a
      transactional disk layer into a layer with one disk.

        * `TxnDiskAPI.v` defines the
          transactional layer.

        * `Impl.v` is the
          write-ahead logging code.

        * `HoareProof.v` is
          the proof of recovery refinement.

        * `ComposedRefinement.v`
          composes the refinement proof with the replicated disk example to
          obtain a refinement from the transactional disk to the two disks.

The `vendor` subdirectory contains various submodules for Coq libraries
that we use in the development. See the README files within each submodule for
documentation.

The `logging-client` subdirectory contains code to extract and
run the composed logging and replication implementation, which provides a
transactional API on top of two unreliable disks. See its separate
`README.md` for details.

# About this artifact

This artifact was prepared by using `argosy/artifact/prepare.sh`, which calls
`argosy/release.sh` to package up the Argosy source code. The release consists
of copying the git repo and then deleting things.

The VM was produced by preparing the artifact and then using the packer setup in
`argosy/artifact/vm` to do an unattended install of Xubuntu and export the
resulting VM in VirtualBox.
