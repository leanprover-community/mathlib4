/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Circle

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

lemma IsCyclic.push_ofSurjective {G H : Type*} [Pow G ℤ] [Pow H ℤ] (h : IsCyclic G)
    (f : G → H) (hf₁ : Function.Surjective f) (hf₂ : ∀ a : G, ∀ n : ℤ, f (a ^ n) = f a ^ n) :
    IsCyclic H where
  exists_zpow_surjective := by
    obtain ⟨g₀, hg₀⟩ := h.exists_zpow_surjective
    use f g₀
    intro w
    obtain ⟨z , hz⟩ := Function.Surjective.comp hf₁ hg₀ w
    exact ⟨z, by rw [← hz, Function.comp_apply]; simp_all only⟩

variable (n : ℕ) [NeZero n]

/-- nth roots of unity of the complex numbers embeded into the Circle -/
noncomputable def rootsOfUnitytoCircle : (rootsOfUnity n ℂ) →* Circle where
  toFun := fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Equivalence of the nth roots of unity of the Circle with nth roots of unity of the complex
numbers -/
noncomputable def rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := (rootsOfUnityUnitsMulEquiv ℂ n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity', MonoidHom.coe_toHomUnits, ← MonoidHom.map_pow,
      ← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

/-
instance : IsCyclic (rootsOfUnity n Circle) where
  exists_zpow_surjective := by
    obtain ⟨g₀, hg₀⟩ := (IsAlgClosed.hasEnoughRootsOfUnity ℂ n).cyc.exists_zpow_surjective
    use (rootsOfUnityCircleEquiv n).symm g₀
    intro w
    obtain ⟨z , hz⟩ := Function.Surjective.comp (rootsOfUnityCircleEquiv n).symm.surjective hg₀ w
    exact ⟨z, by rw [← hz, Function.comp_apply, map_zpow]⟩
-/

lemma pullIsPrimitiveRoot {m : ℂ} (hm : IsPrimitiveRoot m n) :
    IsPrimitiveRoot ((rootsOfUnityCircleEquiv n).symm hm.toRootsOfUnity) n where
  pow_eq_one := by
    have e1 : m ^ n = 1 :=  hm.pow_eq_one
    have e2 : hm.toRootsOfUnity ^ n = 1 := by
      ext : 2
      simp_all only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val,
        IsPrimitiveRoot.val_toRootsOfUnity_coe, OneMemClass.coe_one, Units.val_one]
    have e4 : (rootsOfUnityCircleEquiv n).symm (hm.toRootsOfUnity ^ n) = 1 := by
      aesop
    have e5 : ((rootsOfUnityCircleEquiv n).symm hm.toRootsOfUnity) ^ n = 1 := by
      rw [← map_pow, e4]
    rw [e5]
  dvd_of_pow_eq_one := by
    intro l hl
    rw [← (hm.pow_eq_one_iff_dvd l)]
    --rw [← map_pow] at hl
    have e1 : (hm.toRootsOfUnity ^ l) = (rootsOfUnityCircleEquiv n) 1 := by
      rw [← hl]
      rw [← map_pow]
      rw [MulEquiv.apply_symm_apply]
    have e2 : (hm.toRootsOfUnity ^ l) = 1 := by
      aesop
    have e3 : (hm.toRootsOfUnity ^ l).val.val = 1 := by
      rw [e2]
      norm_cast
    rw [← e3]
    norm_cast

instance : HasEnoughRootsOfUnity Circle n where
  prim := by
    obtain ⟨m, hm⟩ := (IsAlgClosed.hasEnoughRootsOfUnity ℂ n).prim
    use ((rootsOfUnityCircleEquiv n).symm hm.toRootsOfUnity).val.val
    simp_all only [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff]
    exact pullIsPrimitiveRoot n hm
  cyc :=
    (IsAlgClosed.hasEnoughRootsOfUnity ℂ n).cyc.push_ofSurjective (rootsOfUnityCircleEquiv n).symm
      (rootsOfUnityCircleEquiv n).symm.surjective (map_zpow _)
