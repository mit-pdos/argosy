#!/bin/bash

## Put together artifact tarball

src="$1"
out="/tmp/argosy-artifact"

if [ -z "$src" ]; then
  echo "Usage: $0 <path to argosy src>"
  exit 1
fi

rm -rf "$out"
mkdir "$out"

make -C "$src/artifact"

src=$(realpath "$src")
pushd "$out"
# package up argosy.tar.gz
"$src"/release.sh "$src" >/dev/null
tar -xf argosy.tar.gz
rm argosy.tar.gz

cp "$src/artifact/README.html" ./
cp "$src/artifact/loc.sh" ./
popd
find "$out" -type f -name '._*' -delete
tar -czvf "30.tar.gz" -C $(dirname "$out") $(basename "$out")
rm -r "$out"
