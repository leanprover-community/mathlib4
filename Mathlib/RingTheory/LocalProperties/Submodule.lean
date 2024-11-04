/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Local properties of modules and submodules

In this file, we show that several conditions on submodules can be checked on stalks.
-/

open scoped nonZeroDivisors

variable {R A M} [CommRing R] [CommRing A] [AddCommGroup M] [Algebra R A] [Module R M] [Module A M]

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

/-- Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `P` is
included in the localization of `N₂` at `P`, then `N₁ ≤ N₂`. -/
theorem Submodule.le_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) ≤ N₂.localized' (Rₚ P) P.primeCompl (f P)) :
    N₁ ≤ N₂ := by
  intro x hx
  suffices N₂.colon (Submodule.span R {x}) = ⊤ by
    simpa using Submodule.mem_colon.mp
      (show (1 : R) ∈ N₂.colon (Submodule.span R {x}) from this.symm ▸ Submodule.mem_top) x
      (Submodule.mem_span_singleton_self x)
  refine Not.imp_symm (N₂.colon (Submodule.span R {x})).exists_le_maximal ?_
  push_neg
  intro P hP le
  obtain ⟨a, ha, s, e⟩ := h P ⟨x, hx, 1, rfl⟩
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp at ht
  refine (t * s).2 (le (Submodule.mem_colon_singleton.mpr ?_))
  simp only [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ht]
  exact N₂.smul_mem _ ha

/-- Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `P` is equal to
the localization of `N₂` at `P`, then `N₁ = N₂`. -/
theorem Submodule.eq_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) = N₂.localized' (Rₚ P) P.primeCompl (f P)) :
    N₁ = N₂ :=
  le_antisymm (Submodule.le_of_localization_maximal Rₚ Mₚ f fun P _ => (h P).le)
    (Submodule.le_of_localization_maximal Rₚ Mₚ f fun P _ => (h P).ge)

/-- A submodule is trivial if its localization at every maximal ideal is trivial. -/
theorem Submodule.eq_bot_of_localization_maximal (N₁ : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) = ⊥) :
    N₁ = ⊥ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

theorem Submodule.mem_of_localization_maximal (r : M) (N₁ : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P r ∈ N₁.localized' (Rₚ P) P.primeCompl (f P)) :
    r ∈ N₁ := by
  rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Submodule.span_le]
  apply Submodule.le_of_localization_maximal Rₚ Mₚ f
  intro N₂ hJ
  rw [Submodule.localized'_span, Submodule.span_le, Set.image_subset_iff, Set.singleton_subset_iff]
  exact h N₂

include Rₚ in
theorem Module.eq_zero_of_localization_maximal (r : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P r = 0) :
    r = 0 := by
  rw [← Submodule.mem_bot (R := R)]
  apply Submodule.mem_of_localization_maximal Rₚ Mₚ f r ⊥ (by simpa using h)

include Rₚ in
theorem Module.eq_of_localization_maximal (r s : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P r = f P s) :
    r = s := by
  rw [← sub_eq_zero]
  simp_rw [← @sub_eq_zero _ _ (f _ _), ← map_sub] at h
  exact Module.eq_zero_of_localization_maximal Rₚ Mₚ f _ h

include Rₚ f in
theorem Module.subsingleton_of_localization_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
    Subsingleton M := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Rₚ Mₚ f x 0 fun _ _ ↦ Subsingleton.elim _ _
