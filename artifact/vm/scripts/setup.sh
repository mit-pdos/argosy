#!/bin/bash

set -e

## install dependencies
# artifact dependencies
sudo apt-get install -y opam cloc sqlite3 zip
# conveniences for VM
sudo apt-get install -y virtualbox-guest-dkms virtualbox-guest-utils virtualbox-guest-utils vim firefox
# CoqIDE dependencies
sudo apt-get install -y pkg-config libgtksourceview2.0-dev

# install stack
wget -qO- https://get.haskellstack.org/ | sh
stack setup --resolver=lts-13.8

# install Coq
opam init --auto-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released/
opam install -j2 -y coq.8.9.0 coqide

## set up artifact
# we do a build first to set up the stack cache
cd /tmp
unzip /tmp/argosy-artifact.zip
cd /tmp/argosy-artifact/argosy
make -j2
cd logging-client
stack test

cd ~/
unzip /tmp/argosy-artifact.zip
