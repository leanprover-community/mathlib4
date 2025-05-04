/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Instances for HasEnoughRootsOfUnity

We provide an instance for `HasEnoughRootsOfUnity F n` when `F` is an algebraically closed field
and `n` is not divisible by the characteristic. In particular, when `F` has characteristic zero,
this hold for all `n ≠ 0`.

### TODO

Add an instance `HasEnoughRootsOfUnity Circle n` for all `n ≠ 0`.
This is probably easiest via setting up an isomorphism
`rootsOfUnity n Circle ≃* rootsOfUnity n ℂ`.
-/

namespace IsAlgClosed

/-- An algebraically closed field `F` satisfies `HasEnoughRootsOfUnity F n` for all `n`
that are not divisible by the characteristic of `F`. -/
instance hasEnoughRootsOfUnity (F : Type*) [Field F] [IsAlgClosed F] (n : ℕ) [i : NeZero (n : F)] :
    HasEnoughRootsOfUnity F n where
  prim := by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {⟨n, NeZero.pos n⟩} F fun _ h ↦ Set.mem_singleton_iff.mp h ▸ i
    exact IsCyclotomicExtension.exists_prim_root (S := {(⟨n, NeZero.pos n⟩ : ℕ+)}) F rfl
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUnity.isCyclic F n

end IsAlgClosed

variable (n : ℕ) [NeZero n]

@[simps]
noncomputable def rootsOfUnitytoCircle : (rootsOfUnity n ℂ) →* Circle where
  toFun := fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := (rootsOfUnityUnitsMulEquiv ℂ n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity', MonoidHom.coe_toHomUnits, ← MonoidHom.map_pow,
      ← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

instance : HasEnoughRootsOfUnity ℂ n := IsAlgClosed.hasEnoughRootsOfUnity ℂ n

instance : IsCyclic (rootsOfUnity n Circle) where
  exists_zpow_surjective := by
    obtain ⟨g₀, hg₀⟩ := (IsAlgClosed.hasEnoughRootsOfUnity ℂ n).cyc.exists_zpow_surjective
    use (rootsOfUnityCircleEquiv n).symm g₀
    intro w
    obtain ⟨z , hz⟩ := Function.Surjective.comp (rootsOfUnityCircleEquiv n).symm.surjective hg₀ w
    exact ⟨z, by rw [← hz, Function.comp_apply, map_zpow]⟩


/-
instance : HasEnoughRootsOfUnity Circle n where
  prim := sorry
  cyc := by
    obtain ⟨z,hz⟩ := (IsAlgClosed.hasEnoughRootsOfUnity ℂ n).cyc.exists_zpow_surjective
-/
