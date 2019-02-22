#!/bin/sh

set -e

# Produce the checksum hash description

echo "The artifact provides an option of using a VM argosy-vm.ova for dependencies; its md5 is also below."
echo '```'
md5sum 30.tar.gz
cd vm/argosy-vm-ova
md5sum argosy-vm.ova
echo '```'
