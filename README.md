# Argosy: verifying layered storage systems with recovery refinement

[![CI](https://github.com/mit-pdos/argosy/actions/workflows/coq-action.yml/badge.svg)](https://github.com/mit-pdos/argosy/actions/workflows/coq-action.yml)

<p>
  <img src="https://raw.githubusercontent.com/mit-pdos/argosy/master/argosy-logo-200.png" width="150">
</p>

Proving crash safety of systems by proving an implementation refines a
specification. Argosy supports implementing layered storage systems with a
recovery procedure per layer, and modular verification of each layer independent
of the other recovery procedures. Argosy also includes an implementation of
Crash Hoare Logic (CHL), a program logic based on Hoare logic for proving an
invariant for recovery reasoning.

Using Argosy we verified an extended example consisting of a write-ahead log
running on top of a disk replication system. See
[README.md](logging-client/README.md) for details on extracting and running the
example.

## Compiling

We develop Argosy using Coq master. It should also be compatible with Coq 8.12
and 8.13, which are tested as part of continuous integration.

This project uses git submodules to include several dependencies. Before
compiling, run `git submodule update --init --recursive` to set those up.

To compile just run `make` with Coq on your `$PATH`.

Details on extraction for the logging example are in its own
[README.md](logging-client/README.md).
