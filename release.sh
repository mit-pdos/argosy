#!/bin/bash

# Prepare a release tarball

set -e

src="$1"
output_dir=/tmp/argosy

if [ -z "$src" ]; then
  echo "Usage: $0 <argosy src>"
  exit 1
fi

rm -rf "$output_dir"
mkdir "$output_dir"
cp -r "$src/" "$output_dir/"

rm "$output_dir/.travis.yml"
rm -r "$output_dir/.github"
rm "$output_dir/src/.dir-locals.el"

# clean build outputs and untracked files
make -C "$output_dir" clean
git -C "$output_dir" clean -fxd

# remove git repo
find "$output_dir" -name '.git' -exec rm -r {} \;
find "$output_dir" -name '.gitignore' -exec rm {} \;

# package
tar -czvf argosy.tar.gz -C $(dirname "$output_dir") $(basename "$output_dir")
rm -r "$output_dir"
