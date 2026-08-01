#!/usr/bin/env bash
# Install the verifier toolchain used by the current lean-eval workspaces.
#
# Usage:
#   bash scripts/setup_lean_eval_tools.sh /path/to/tool-cache \
#     LeanEval/jordan_curve/lean-toolchain
#
# Add the four printed bin directories to PATH, then run `lake test` from a
# problem workspace.  The pins mirror leanprover/lean-eval's documented CI
# setup; keep them immutable and update them deliberately.
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 TOOL_CACHE WORKSPACE_LEAN_TOOLCHAIN" >&2
  exit 2
fi

TOOLS_ROOT="$1"
WORKSPACE_TOOLCHAIN="$2"

LANDRUN_PIN="5ed4a3db3a4ad930d577215c6b9abaa19df7f99f"
LEAN4EXPORT_PIN="4e7915201d3f9f04470d9eae002fa695f7cdc589"
COMPARATOR_PIN="71b52ec29e06d4b7d882726553b1ceb99a2499e0"
NANODA_PIN="68d5ca9db226849b41a6fff59d796ff19d0a8840"

mkdir -p "$TOOLS_ROOT/bin"

checkout_pinned() {
  local url="$1"
  local destination="$2"
  local revision="$3"
  if [[ ! -d "$destination/.git" ]]; then
    git clone --filter=blob:none "$url" "$destination"
  fi
  if [[ "$(git -C "$destination" rev-parse HEAD)" != "$revision" ]]; then
    git -C "$destination" fetch --depth 1 origin "$revision"
    git -C "$destination" checkout --detach "$revision"
  fi
}

GOBIN="$TOOLS_ROOT/bin" go install \
  "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_PIN"

checkout_pinned \
  "https://github.com/leanprover/lean4export.git" \
  "$TOOLS_ROOT/lean4export" "$LEAN4EXPORT_PIN"
if ! cmp -s "$WORKSPACE_TOOLCHAIN" "$TOOLS_ROOT/lean4export/lean-toolchain"; then
  cp "$WORKSPACE_TOOLCHAIN" "$TOOLS_ROOT/lean4export/lean-toolchain"
  (cd "$TOOLS_ROOT/lean4export" && lake clean)
fi
(cd "$TOOLS_ROOT/lean4export" && lake build lean4export)

checkout_pinned \
  "https://github.com/leanprover/comparator.git" \
  "$TOOLS_ROOT/comparator" "$COMPARATOR_PIN"
(cd "$TOOLS_ROOT/comparator" && lake build comparator)

checkout_pinned \
  "https://github.com/robsimmons/nanoda_lib.git" \
  "$TOOLS_ROOT/nanoda" "$NANODA_PIN"
cargo build --release --manifest-path "$TOOLS_ROOT/nanoda/Cargo.toml"

echo "lean-eval verifier tools are ready; add these directories to PATH:"
echo "  $TOOLS_ROOT/bin"
echo "  $TOOLS_ROOT/lean4export/.lake/build/bin"
echo "  $TOOLS_ROOT/comparator/.lake/build/bin"
echo "  $TOOLS_ROOT/nanoda/target/release"
