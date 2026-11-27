#!/usr/bin/env bash
set -eu

repo=$(cd "$(dirname "$0")/../.." && pwd)
project=$(mktemp -d)
trap 'rm -rf "$project"' EXIT
cd "$project"
cp "$repo/lean-toolchain" .

cat > lakefile.toml <<'EOF'
name = "example"
defaultTargets = ["Example"]
[[lean_lib]]
name = "Example"
EOF

cat > Example.lean <<'EOF'
def New.fresh : Nat := 42

namespace Old
def fresh : Nat := 7
def New.fresh : Nat := 3
@[deprecated _root_.New.fresh (since := "2025-01-01")]
def stale := _root_.New.fresh
def caller := stale
end Old

#guard Old.caller == 42

structure Box where
  n : Nat
def Box.fresh (b : Box) := b.n
@[deprecated Box.fresh (since := "2025-01-01")]
def Box.stale (b : Box) := Box.fresh b
def field (b : Box) := b.stale

def moved (b : Box) := b.n
@[deprecated moved (since := "2025-01-01")]
def Box.old (b : Box) := moved b
def movedField (b : Box) := b.old
EOF

lake build
python3 "$repo/scripts/fix_deprecations.py"
grep -Fxq 'def caller := _root_.New.fresh' Example.lean
grep -Fxq 'def field (b : Box) := b.fresh' Example.lean
grep -Fxq 'def movedField (b : Box) := b.old' Example.lean
lake build
