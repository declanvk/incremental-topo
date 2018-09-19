#!/usr/bin/env bash

# Exit on error. Append "|| true" if you expect an error.
set -o errexit
# Exit on error inside any functions or subshells.
set -o errtrace
# Do not allow use of undefined vars. Use ${VAR:-} to use an undefined VAR
set -o nounset
# Catch the error in case mysqldump fails (but gzip succeeds) in `mysqldump |gzip`
set -o pipefail

CRATESIO_VERSION=$(cargo search incremental-topo | cut -d "\"" -f2) || "CRATESIO_VERSION FAILED"
LOCAL_VERSION=$(cargo read-manifest | jq -r .version) || "LOCAL_VERSION FAILED"

if [[ "$CRATESIO_VERSION" == "$LOCAL_VERSION" ]]; then
  printf "Crate version not changed locally"
  exit
else
  git tag -a "v$LOCAL_VERSION" -m "Version $LOCAL_VERSION of incremental-topo"

  cargo publish --dry-run
fi
