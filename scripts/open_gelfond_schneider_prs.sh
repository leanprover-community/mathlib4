#!/usr/bin/env bash
# Open/update the stacked Gelfond–Schneider PRs on leanprover-community/mathlib4.
# Requires: gh auth login (token must be valid)
set -euo pipefail

REPO=leanprover-community/mathlib4
FORK=mkaratarakis

if ! gh auth status -h github.com >/dev/null 2>&1; then
  echo "Run: gh auth login -h github.com"
  exit 1
fi

# Ensure branches are pushed to the fork
git push git@github.com:${FORK}/mathlib4.git \
  nat-denominator gs-isintegral-cast gs-house-siegel gs-mainalg 2>/dev/null || true

# --- PR 2: IsIntegral helpers (update #39873 if it exists, else create) ---
ISINTEGRAL_BODY="$(cat <<'EOF'
## Summary

This PR adds small integrality lemmas for literals in number fields:

- `IsIntegral.Cast`: every integer embeds integrally into a field
- `IsIntegral.Nat`: every natural number embeds integrally into a field

These are used when clearing denominators and bounding houses in the
Gelfond–Schneider development.

## Dependencies

- [ ] depends on: #39872

## Test plan

- [x] `lake env lean Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`

---

Supersedes the `IntegralClosure` portion of #35733. Part of the split Gelfond–Schneider stack:

1. #39872 — `natDenominator` API
2. **this PR** — `IsIntegral` helpers
3. `gs-house-siegel` — Siegel / house infrastructure
4. `gs-mainalg` — `GelfondSchneider.MainAlg`
EOF
)"

if gh pr view 39873 --repo "$REPO" >/dev/null 2>&1; then
  gh pr edit 39873 --repo "$REPO" \
    --base nat-denominator \
    --title "feat(RingTheory/IntegralClosure): add IsIntegral helpers for casts" \
    --body "$ISINTEGRAL_BODY"
  PR2=39873
  echo "Updated PR #$PR2"
else
  PR2=$(gh pr create --repo "$REPO" \
    --base nat-denominator \
    --head "${FORK}:gs-isintegral-cast" \
    --title "feat(RingTheory/IntegralClosure): add IsIntegral helpers for casts" \
    --body "$ISINTEGRAL_BODY" \
    | tail -1 | grep -oE '[0-9]+$')
  echo "Created PR #$PR2"
fi

# --- PR 3: House / Siegel infrastructure ---
HOUSE_BODY="$(cat <<EOF
## Summary

Refactors \`NumberField.House\` to expose the Siegel-lemma infrastructure used in
Gelfond–Schneider:

- rename the private basis-matrix bound \`c\` to \`basisMatrixInvSupNorm\`
- make \`house\` an \`abbrev\` (reducible) for downstream rewriting
- adjust \`exists_ne_zero_int_vec_house_le\` and related \`c₁\` / \`c₂\` API

No Gelfond–Schneider-specific definitions live here; this is reusable Siegel setup.

## Dependencies

- [ ] depends on: #39872
- [ ] depends on: #${PR2}

## Test plan

- [x] \`lake env lean Mathlib/NumberTheory/NumberField/House.lean\`

---

Supersedes the \`House\` portion of #35733.
EOF
)"

if gh pr view --repo "$REPO" --head "${FORK}:gs-house-siegel" --json number -q .number 2>/dev/null | grep -q .; then
  PR3=$(gh pr view --repo "$REPO" --head "${FORK}:gs-house-siegel" --json number -q .number)
  gh pr edit "$PR3" --repo "$REPO" \
    --base gs-isintegral-cast \
    --title "refactor(NumberField/House): expose Siegel lemma infrastructure" \
    --body "$HOUSE_BODY"
  echo "Updated PR #$PR3"
else
  PR3=$(gh pr create --repo "$REPO" \
    --base gs-isintegral-cast \
    --head "${FORK}:gs-house-siegel" \
    --title "refactor(NumberField/House): expose Siegel lemma infrastructure" \
    --body "$HOUSE_BODY" \
    | tail -1 | grep -oE '[0-9]+$')
  echo "Created PR #$PR3"
fi

# --- PR 4: MainAlg ---
MAINALG_BODY="$(cat <<EOF
## Summary

Adds \`Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAlg\`: the algebraic
setup for Gelfond–Schneider (Hilbert's seventh problem):

- common number field and parameters \`h\`, \`m\`, \`n\`
- denominator clearing via \`c₁\` and the scaled Siegel matrix \`A\`
- house-norm bounds (\`house_matrixA_le\`, \`house_eta_le_c₄_pow\`) for Siegel's lemma

The transcendence proof itself is in later files.

## Dependencies

- [ ] depends on: #39872 (\`natDenominator\` API)
- [ ] depends on: #${PR2} (\`IsIntegral\` helpers)
- [ ] depends on: #${PR3} (Siegel / house infrastructure)

## Test plan

- [x] \`lake env lean Mathlib/NumberTheory/Transcendental/GelfondSchneider/MainAlg.lean\`

---

**Please close #35733** — it duplicated this stack against \`master\`.
Stacked on \`gs-house-siegel\`; merge in order after dependencies land.
EOF
)"

if gh pr view --repo "$REPO" --head "${FORK}:gs-mainalg" --json number -q .number 2>/dev/null | grep -q .; then
  PR4=$(gh pr view --repo "$REPO" --head "${FORK}:gs-mainalg" --json number -q .number)
  gh pr edit "$PR4" --repo "$REPO" \
    --base gs-house-siegel \
    --title "feat(GelfondSchneider): add MainAlg Siegel matrix setup" \
    --body "$MAINALG_BODY"
  echo "Updated PR #$PR4"
else
  PR4=$(gh pr create --repo "$REPO" \
    --base gs-house-siegel \
    --head "${FORK}:gs-mainalg" \
    --title "feat(GelfondSchneider): add MainAlg Siegel matrix setup" \
    --body "$MAINALG_BODY" \
    | tail -1 | grep -oE '[0-9]+$')
  echo "Created PR #$PR4"
fi

echo ""
echo "Stack (merge in order):"
echo "  #39872  nat-denominator → master"
echo "  #${PR2}  gs-isintegral-cast → nat-denominator"
echo "  #${PR3}  gs-house-siegel → gs-isintegral-cast"
echo "  #${PR4}  gs-mainalg → gs-house-siegel"
echo ""
echo "Close #35733 manually if still open."
