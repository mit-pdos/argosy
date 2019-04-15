#!/bin/bash

## Put together artifact tarball

src="$1"
submission_pdf="$2"
out="/tmp/argosy-artifact"
out_dir="$PWD"

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

# package up the rest of the artifact
cp "$src/artifact/README.html" ./
cp "$src/artifact/loc.sh" ./
cp "$submission_pdf" ./argosy-submission.pdf
popd
find "$out" -type f -name '._*' -delete

# Note that the uploaded artifact needs to be a zip file because HotCRP
# doesn't preserve the tar part of the filename for compressed tarballs.
pushd "$out/.."
rm -f "$out_dir/argosy-artifact.zip"
zip -r "$out_dir/argosy-artifact.zip" $(basename "$out")
popd
rm -r "$out"
