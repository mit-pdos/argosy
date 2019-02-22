#!/bin/bash

# Get lines of code, organized into some categories.
#
# Depends on cloc and sqlite3.
#
# Usage: loc.sh <path to argosy>

set -e

error() {
  echo "$1" >&2
}

header() {
  echo -e "\033[1;37m$1\033[0m"
}

underline() {
  echo "============"
}

main() {
  local show_files=true
  local ARGOSY_SRC="$1"
  if [ ! -d "$ARGOSY_SRC" ]; then
    error "Usage: $0 <path to argosy>"
    exit 1
  fi

  local tmp_db=$(mktemp -t "cloc-XXX.sqlite3")
  cd "${ARGOSY_SRC}"
  cloc --quiet --sql="-" --include-lang=Coq,Haskell src logging-client vendor | sqlite3 "$tmp_db"

  get_totals() {
    sqlite3 -cmd ".mode line" "$tmp_db" \
            "select cast(round(sum(nCode)/10)*10 as int) as \"LOC\",
                    count(File) as \"files\" from t where ($1);"
    if [ "$show_files" = true ]; then
      sqlite3 "$tmp_db" -cmd ".separator \", \"" "select File, nCode from t where ($1) order by File;"
    fi
  }

  header "Core framework"
  get_totals 'File_dirname glob "src/Spec*"';

  echo
  header "External libraries (minus Array)"
  get_totals '(File_dirname glob "vendor/*"
    AND NOT File_dirname glob "vendor/array/*")'

  echo
  header "Relation algebra library"
  get_totals 'File_basename glob "Relation*.v"'

  echo
  header "Argosy total"
  get_totals '(File_dirname glob "src/Spec*"
           OR File_dirname glob "vendor/*"
           OR File glob "src/Helpers/Relation*.v")
           AND NOT File_dirname glob "vendor/array/*"'

  echo
  header "Examples:"
  underline
  header "Array"
  get_totals 'File_dirname glob "vendor/array/*"'

  echo
  header "Disk replication"
  get_totals '(File_dirname glob "src/Examples/ReplicatedDisk*"
    OR File_basename = "Disk.v"
    OR File_basename = "Maybe.v")'

  echo
  header "Logging"
  get_totals 'File_dirname glob "src/Examples/Logging*"'

  echo
  header "Examples total"
  get_totals 'File_dirname glob "vendor/array/*"
            OR File_dirname glob "src/Examples/ReplicatedDisk*"
            OR File_basename = "Disk.v"
            OR File_basename = "Maybe.v"
            OR File_dirname glob "src/Examples/Logging*"'

  echo
  header "Other things"
  underline
  header "StatDB"
  get_totals 'File_dirname glob "src/Examples/StatDb*"'


  echo
  header "Haskell logging-client"
  get_totals '(File_dirname glob "logging-client/src/*")'

  rm "$tmp_db"
}

main "$@"
