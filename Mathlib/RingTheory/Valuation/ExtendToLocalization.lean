/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Valuation.Basic

#align_import ring_theory.valuation.extend_to_localization from "leanprover-community/mathlib"@"64b3576ff5bbac1387223e93988368644fcbcd7e"

/-!

# Extending valuations to a localization

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.primeCompl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/


variable {A : Type*} [CommRing A] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation A Γ) {S : Submonoid A} (hS : S ≤ v.supp.primeCompl) (B : Type*) [CommRing B]
  [Algebra A B] [IsLocalization S B]

/-- We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`. -/
noncomputable def Valuation.extendToLocalization : Valuation B Γ :=
  let f := IsLocalization.toLocalizationMap S B
  let h : ∀ s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert f.lift_eq (P := Γ) _ 0 <;> simp
                    -- ⊢ 0 = ↑(Submonoid.LocalizationMap.toMap f) 0
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
    map_add_le_max' := fun x y => by
      obtain ⟨a, b, s, rfl, rfl⟩ : ∃ (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y := by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t
        constructor <;>
          · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]
            ring_nf
      convert_to f.lift h (f.mk' (a + b) s) ≤ max (f.lift h _) (f.lift h _)
      -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := src✝.toFun, map_zero' := (_ : OneH …
      · refine' congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 _)
        -- ⊢ (Submonoid.LocalizationMap.mk' f a s + Submonoid.LocalizationMap.mk' f b s)  …
        rw [add_mul, _root_.map_add]
        -- ⊢ Submonoid.LocalizationMap.mk' f a s * ↑(algebraMap A B) ↑s + Submonoid.Local …
        iterate 2 erw [IsLocalization.mk'_spec]
        -- 🎉 no goals
      iterate 3 rw [f.lift_mk']
      -- ⊢ ↑↑v.toMonoidWithZeroHom (a + b) * ↑(↑(IsUnit.liftRight (MonoidHom.restrict ( …
      rw [max_mul_mul_right]
      -- ⊢ ↑↑v.toMonoidWithZeroHom (a + b) * ↑(↑(IsUnit.liftRight (MonoidHom.restrict ( …
      apply mul_le_mul_right' (v.map_add a b) }
      -- 🎉 no goals
#align valuation.extend_to_localization Valuation.extendToLocalization

@[simp]
theorem Valuation.extendToLocalization_apply_map_apply (a : A) :
    v.extendToLocalization hS B (algebraMap A B a) = v a :=
  Submonoid.LocalizationMap.lift_eq _ _ a
#align valuation.extend_to_localization_apply_map_apply Valuation.extendToLocalization_apply_map_apply
