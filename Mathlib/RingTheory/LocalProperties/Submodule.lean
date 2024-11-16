/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Local properties of modules and submodules

In this file, we show that several conditions on submodules can be checked on stalks.
-/

open scoped nonZeroDivisors

variable {R A M} [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
  [Algebra R A] [Module R M] [Module A M]

variable
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

theorem Module.eq_of_localization_maximal (m m' : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m = f P m') :
    m = m' := by
  by_contra! ne
  rw [← one_smul R m, ← one_smul R m'] at ne
  let I : Ideal R :=
  { carrier := {r : R | r • m = r • m'}
    add_mem' := fun h h' ↦ by simpa [add_smul] using congr($h + $h')
    zero_mem' := by simp_rw [Set.mem_setOf, zero_smul]
    smul_mem' := fun _ _ h ↦ by simpa [mul_smul] using congr(_ • $h) }
  have ⟨P, mP, le⟩ := I.exists_le_maximal (I.ne_top_iff_one.mpr ne)
  have ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists P.primeCompl _).mp (h P)
  exact s.2 (le hs)

theorem Module.eq_zero_of_localization_maximal (m : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m = 0) :
    m = 0 :=
  eq_of_localization_maximal _ f _ _ fun P _ ↦ by rw [h, map_zero]

theorem Submodule.mem_of_localization_maximal (m : M) (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m ∈ N.localized₀ P.primeCompl (f P)) :
    m ∈ N := by
  let I : Ideal R :=
  { carrier := { r : R | r • m ∈ N }
    add_mem' := fun h h' ↦ by simpa [add_smul] using add_mem h h'
    zero_mem' := by simp
    smul_mem' := fun _ _ h ↦ by simpa [mul_smul] using smul_mem _ _ h }
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  refine Not.imp_symm I.exists_le_maximal fun ⟨P, hP, le⟩ ↦ ?_
  obtain ⟨a, ha, s, e⟩ := h P
  rw [← IsLocalizedModule.mk'_one P.primeCompl, IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp_rw [smul_smul] at ht
  exact (t * s).2 (le <| by apply ht ▸ smul_mem _ _ ha)

/-- Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `P` is
included in the localization of `N₂` at `P`, then `N₁ ≤ N₂`. -/
theorem Submodule.le_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) ≤ N₂.localized₀ P.primeCompl (f P)) :
    N₁ ≤ N₂ :=
  fun m hm ↦ mem_of_localization_maximal _ f _ _ fun P hP ↦ h P ⟨m, hm, 1, by simp⟩

/-- Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `P` is equal to
the localization of `N₂` at `P`, then `N₁ = N₂`. -/
theorem Submodule.eq_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) = N₂.localized₀ P.primeCompl (f P)) :
    N₁ = N₂ :=
  le_antisymm (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).le)
    (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).ge)

/-- A submodule is trivial if its localization at every maximal ideal is trivial. -/
theorem Submodule.eq_bot_of_localization_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization_maximal Mₚ f fun P hP ↦ by simpa using h P

include f in
theorem Module.subsingleton_of_localization_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
    Subsingleton M := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Mₚ f x 0 fun _ _ ↦ Subsingleton.elim _ _
