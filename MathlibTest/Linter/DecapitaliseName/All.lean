-- import Mathlib
import Mathlib.Tactic.Linter.DecapitaliseName

open Lean

/--
info: ❌ `count_le_setENCard` → `count_le_setEncard`
---
info: ❌ `aestronglyMeasurable_fun_sum` → `aeStronglyMeasurable_fun_sum`
---
info: ❌ `coeLinearMap_eq_dfinsuppSum` → `coeLinearMap_eq_dFinsuppSum`
---
info: ❌ `SpecMap_residue` → `specMap_residue`
---
info: ✅ `δ₀Iter_zero`
---
info: ✅ `trans_wSameSide`
---
info: ❌ `Faithful` → `faithful`
---
info: ❌ `eq_of_IsDetpBalanced` → `eq_of_isDetpBalanced`
---
info: ❌ `AB5StarOfSize_shrink` → `ab5StarOfSize_shrink`
---
info: ✅ `d_ιE_fromOpcycles_assoc`
---
info: ✅ `app_ΓIso_hom_apply`
---
info: ❌ `local_hom_TFAE` → `local_hom_tfae`
-/
#guard_msgs in
run_meta
  let env ← getEnv
  let names := [
    ``Nat.count_le_setENCard,
    ``Multiset.aestronglyMeasurable_fun_sum,
    ``MvPolynomial.DirectSum.coeLinearMap_eq_dfinsuppSum,
    ``AlgebraicGeometry.IsClosedImmersion.SpecMap_residue,
    ``CategoryTheory.SimplicialObject.δ₀Iter_zero,
    ``AffineSubspace.SSameSide.trans_wSameSide,
    ``CategoryTheory.ReflQuiv.forget.Faithful,
    ``Matrix.Nonsingular.eq_of_IsDetpBalanced,
    ``CategoryTheory.AB5StarOfSize_shrink,
    ``CategoryTheory.Abelian.SpectralObject.d_ιE_fromOpcycles_assoc,
    ``AlgebraicGeometry.IsOpenImmersion.app_ΓIso_hom_apply,
    ``IsLocalRing.local_hom_TFAE,
  ]
  for name in names do
    let newName ← name.suggestTheoremName env
    match newName with
    | some newName => logInfo m!"❌ `{name.lastComponentAsString}` → `{newName}`"
    | none => logInfo m!"✅ `{name.lastComponentAsString}`"

/-- info: 5995 theorems to rename -/
#guard_msgs in
run_meta
  let mut n : Nat := 0
  let env ← getEnv
  let mods := env.allImportedModuleNames
  for (name, _) in env.constants.map₁ do
    let moduleIdx := env.getModuleIdxFor? name |>.getD default
    let moduleName := mods[moduleIdx]!
    unless moduleName.getRoot == `Mathlib do continue
    if name.isInternalDetail then continue
    if (← Batteries.Tactic.Lint.isAutoDecl name) then continue
    if Linter.isDeprecated env name then continue
    let some _ ← name.suggestTheoremName env | continue
    n := n + 1
  logInfo m!"{n} theorems to rename"
