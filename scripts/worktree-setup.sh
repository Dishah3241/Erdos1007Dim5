#!/usr/bin/env bash
# Link this worktree's Mathlib to the primary checkout's, so a worker never downloads a fresh
# 7.4 GB `.lake/packages` per worktree. Run it once, before the first `lake` command, in any
# linked worktree of this project; in the primary checkout it does nothing.
#
# Usage: scripts/worktree-setup.sh

set -euo pipefail

root=$(git rev-parse --show-toplevel)
common=$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)
primary=$(dirname "$common")

if [[ "$primary" == "$root" ]]; then
  echo "worktree-setup: primary checkout; nothing to link"
  exit 0
fi

source_packages="$primary/.lake/packages"
if [[ ! -d "$source_packages" ]]; then
  echo "worktree-setup: $source_packages is missing; build the primary checkout first" >&2
  exit 1
fi
source_packages=$(cd "$source_packages" && pwd -P)

mkdir -p "$root/.lake"
if [[ -L "$root/.lake/packages" ]]; then
  echo "worktree-setup: already linked to $(readlink "$root/.lake/packages")"
  exit 0
fi
if [[ -e "$root/.lake/packages" ]]; then
  echo "worktree-setup: $root/.lake/packages exists as a real directory; leaving it" >&2
  exit 1
fi
ln -s "$source_packages" "$root/.lake/packages"
echo "worktree-setup: linked .lake/packages -> $source_packages"
