#!/bin/bash

set -e

# install stack
wget -qO- https://get.haskellstack.org/ | sh
stack setup --resolver=lts-13.8

# install Coq
opam init --auto-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released/
opam install -j2 -y coq.8.9.0

# set up artifact
cd ~/
tar -xf /tmp/argosy-artifact.tar.gz
