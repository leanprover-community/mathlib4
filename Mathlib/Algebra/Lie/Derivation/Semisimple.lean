/-
Copyright © 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
import Mathlib.Algebra.Lie.Derivation.AdjointAction
import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Derivations of finite dimensional Killing Lie algebras

This file establishes that all derivations of finite-dimensional Killing Lie algebras are inner.

## Main statements

The following statements hold for a finite-dimensional Lie algebra `L` with non-degenerate Killing
form.

- `LieDerivation.Killing.ad_injective`: the adjoint action is injective,
- `LieDerivation.Killing.equiv_rangeAd`: `L` is isomorphic to its adjoint representation,
- `LieDerivation.Killing.rangeAd_eq_top`: the range of the adjoint action is full,
- `LieDerivation.Killing.exists_eq_ad`: any derivation is an inner derivation.
-/

namespace LieDerivation.Killing

section

variable (R L : Type*) [Field R] [LieRing L]
  [LieAlgebra R L] [Module.Finite R L] [LieAlgebra.IsKilling R L]

/-- A local notation for the set of (Lie) derivations on `L`. -/
local notation "𝔻" => (LieDerivation R L L)

/-- A local notation for the ideal range of `ad`. -/
local notation "𝕀" => LieHom.idealRange (ad R L)

/-- A local notation for the Killing complement of the ideal range of `ad`. -/
local notation "𝕀ᗮ" => LieIdeal.killingCompl R 𝔻 𝕀

/-- The adjoint action on a finite-dimensional Killing Lie algebra is injective. -/
lemma ad_injective : Function.Injective (ad R L) := by
  apply (LieHom.ker_eq_bot (ad R L)).mp
  rw [ad_ker_eq_center, LieAlgebra.center_eq_bot_of_semisimple]

/-- The Lie algebra isomorphism between a finite-dimensional Killing Lie algebra and its adjoint
representation. -/
noncomputable def equiv_rangeAd : L ≃ₗ⁅R⁆ (ad R L).idealRange := by
  have h := LieEquiv.ofInjective (ad R L) (ad_injective R L)
  rw [← ad_isIdealMorphism] at h
  exact h

/-- The restriction of the Killing form of a finite-dimensional Killing Lie algebra to the range of
the adjoint action is nondegenerate. -/
lemma killingForm_nondegenerate_on_rangeAd :
    ((killingForm R 𝔻).restrict (lieIdealSubalgebra R 𝔻 𝕀).toSubmodule).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
  rw [← LieIdeal.killingForm_eq]
  have _ : LieAlgebra.IsKilling R (lieIdealSubalgebra R 𝔻 𝕀) := (equiv_rangeAd R L).isKilling
  rw [← LieAlgebra.IsKilling.ker_killingForm_eq_bot]
  exact rfl

/-- In a finite-dimensional Killing Lie algebra, the range of the adjoint action and its Killing
complement are complements. -/
lemma isCompl_rangeAd : IsCompl 𝕀 𝕀ᗮ := by
  apply IsCompl.of_orderEmbedding (LieSubmodule.toSubmodule_orderEmbedding R 𝔻 𝔻)
  simp_rw [LieSubmodule.toSubmodule_orderEmbedding_apply]
  rw [LieIdeal.killingCompl_eq_orthogonalBilin]
  exact LinearMap.BilinForm.restrict_nondegenerate_of_isCompl_orthogonal
    (LinearMap.IsSymm.isRefl (LieModule.traceForm_isSymm R 𝔻 𝔻))
    (killingForm_nondegenerate_on_rangeAd R L)

/-- In a finite-dimensional Killing Lie algebra, the Killing complement of the range of the adjoint
action is trivial. -/
lemma compl_rangeAd_eq_bot : 𝕀ᗮ = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  intro D hD
  ext x
  apply ad_injective R L
  rw [zero_apply, LieHom.map_zero, ← lie_der_ad_eq_ad_der]
  have h1 : ⁅D, ad R L x⁆ ∈ 𝕀ᗮ := lie_mem_left _ _ _ _ _ hD
  have h2 : ⁅D, ad R L x⁆ ∈ 𝕀 := lie_mem_right _ _ _ _ _ (LieHom.mem_idealRange (ad R L) x)
  have h3 : ⁅D, ad R L x⁆ ∈ 𝕀 ⊓ 𝕀ᗮ := ⟨h2, h1⟩
  rw [IsCompl.inf_eq_bot (isCompl_rangeAd R L)] at h3
  exact h3

/-- The range of the adjoint action on a finite-dimensional Killing Lie algebra is full. -/
theorem rangeAd_eq_top : 𝕀 = ⊤ := by
  apply eq_top_of_isCompl_bot
  rw [← compl_rangeAd_eq_bot R L]
  exact isCompl_rangeAd R L

variable {R L} in
/-- Every derivation of a finite-dimensional Killing Lie algebra is an inner derivation. -/
lemma exists_eq_ad (D : 𝔻) : ∃ x, ad R L x = D := by
  rw [← mem_ad_idealRange_iff, rangeAd_eq_top R L]
  exact trivial

end
