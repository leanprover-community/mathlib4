#!/bin/bash
set -e

# create file via EOF
mkdir -p Mathlib/Algebra
cat > Mathlib/Algebra/MyNewProofs.lean << 'EOF'
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

theorem my_add_comm (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b
EOF

# git workflow
git checkout -b feature/your-proofs || git checkout feature/your-proofs
git add .
git commit -m "feat: add MyNewProofs automatically via Termux EOF"
git push -u origin feature/your-proofs

# open PR
gh pr create --base leanprover-community:master \
  --head batmeezy918:feature/your-proofs \
  --title "Add MyNewProofs" \
  --body "Automated PR from Termux using EOF-generated file"
