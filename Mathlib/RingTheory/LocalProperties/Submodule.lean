/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Local properties of modules and submodules

In this file, we show that several conditions on submodules can be checked on stalks.
-/

open scoped nonZeroDivisors

variable {R M M₁ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₁] [Module R M₁]

section maximal

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
  (M₁ₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (M₁ₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (M₁ₚ P)]
  (f₁ : ∀ (P : Ideal R) [P.IsMaximal], M₁ →ₗ[R] M₁ₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f₁ P)]

theorem Submodule.mem_of_localization_maximal (m : M) (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m ∈ N.localized₀ P.primeCompl (f P)) :
    m ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
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
theorem Submodule.eq_of_localization₀_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) = N₂.localized₀ P.primeCompl (f P)) :
    N₁ = N₂ :=
  le_antisymm (Submodule.le_of_localization_maximal Mₚ f fun P _ ↦ (h P).le)
    (Submodule.le_of_localization_maximal Mₚ f fun P _ ↦ (h P).ge)

/-- A submodule is trivial if its localization at every maximal ideal is trivial. -/
theorem Submodule.eq_bot_of_localization₀_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization₀_maximal Mₚ f fun P hP ↦ by simpa using h P

theorem Submodule.eq_top_of_localization₀_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊤) :
    N = ⊤ :=
  Submodule.eq_of_localization₀_maximal Mₚ f fun P hP ↦ by simpa using h P

theorem Module.eq_of_localization_maximal (m m' : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m = f P m') :
    m = m' := by
  rw [← one_smul R m, ← one_smul R m']
  by_contra ne
  have ⟨P, mP, le⟩ := (eqIdeal R m m').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists P.primeCompl _).mp (h P)
  exact s.2 (le hs)

theorem Module.eq_zero_of_localization_maximal (m : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m = 0) :
    m = 0 :=
  eq_of_localization_maximal _ f _ _ fun P _ ↦ by rw [h, map_zero]

theorem LinearMap.eq_of_localization_maximal (g g' : M →ₗ[R] M₁)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g =
      IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g') :
    g = g' :=
  ext fun x ↦ Module.eq_of_localization_maximal _ f₁ _ _ fun P _ ↦ by
    simpa only [IsLocalizedModule.map_apply] using DFunLike.congr_fun (h P) (f P x)

include f in
theorem Module.subsingleton_of_localization_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
    Subsingleton M := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Mₚ f x 0 fun _ _ ↦ Subsingleton.elim _ _

theorem Submodule.eq_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) = N₂.localized' (Rₚ P) P.primeCompl (f P)) :
    N₁ = N₂ :=
  eq_of_localization₀_maximal Mₚ f fun P _ ↦ congr(restrictScalars _ $(h P))

theorem Submodule.eq_bot_of_localization_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP ↦ by simpa using h P

theorem Submodule.eq_top_of_localization_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊤) :
    N = ⊤ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP ↦ by simpa using h P

end maximal

section span

open IsLocalizedModule LocalizedModule Ideal

variable (s : Set R) (span_eq : Ideal.span s = ⊤)
include span_eq

variable
  (Rₚ : ∀ _ : s, Type*)
  [∀ r : s, CommSemiring (Rₚ r)]
  [∀ r : s, Algebra R (Rₚ r)]
  [∀ r : s, IsLocalization.Away r.1 (Rₚ r)]
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  [∀ r : s, Module (Rₚ r) (Mₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (f r)]

theorem Module.eq_of_isLocalized_span (x y : M) (h : ∀ r : s, f r x = f r y) : x = y := by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalizedModule.eq_iff_exists (.powers r.1) _).mp (h r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩

theorem Module.eq_zero_of_isLocalized_span (x : M) (h : ∀ r : s, f r x = 0) : x = 0 :=
  eq_of_isLocalized_span s span_eq _ f x 0 <| by simpa only [map_zero] using h

theorem Submodule.mem_of_isLocalized_span {m : M} {N : Submodule R M}
    (h : ∀ r : s, f r m ∈ N.localized₀ (.powers r.1) (f r)) : m ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  by_contra! ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  obtain ⟨a, ha, t, e⟩ := h r
  rw [← IsLocalizedModule.mk'_one (.powers r.1), IsLocalizedModule.mk'_eq_mk'_iff] at e
  have ⟨u, hu⟩ := e
  simp_rw [smul_smul] at hu
  exact Set.disjoint_right.mp disj (u * t).2 (by apply hu ▸ smul_mem _ _ ha)

theorem Submodule.le_of_isLocalized_span {N P : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) ≤ P.localized₀ (.powers r.1) (f r)) : N ≤ P :=
  fun m hm ↦ mem_of_isLocalized_span s span_eq _ f fun r ↦ h r ⟨m, hm, 1, by simp⟩

theorem Submodule.eq_of_isLocalized₀_span {N P : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) = P.localized₀ (.powers r.1) (f r)) : N = P :=
  le_antisymm (le_of_isLocalized_span s span_eq _ _ fun r ↦ (h r).le)
    (le_of_isLocalized_span s span_eq _ _ fun r ↦ (h r).ge)

theorem Submodule.eq_bot_of_isLocalized₀_span {N : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_isLocalized₀_span s span_eq Mₚ f fun _ ↦ by simp only [h, Submodule.localized₀_bot]

theorem Submodule.eq_top_of_isLocalized₀_span {N : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_isLocalized₀_span s span_eq Mₚ f fun _ ↦ by simp only [h, Submodule.localized₀_top]

theorem Submodule.eq_of_isLocalized'_span {N P : Submodule R M}
    (h : ∀ r, N.localized' (Rₚ r) (.powers r.1) (f r) = P.localized' (Rₚ r) (.powers r.1) (f r)) :
    N = P :=
  eq_of_isLocalized₀_span s span_eq _ f fun r ↦ congr(restrictScalars _ $(h r))

theorem Submodule.eq_bot_of_isLocalized'_span {N : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ ↦ by simp only [h, Submodule.localized'_bot]

theorem Submodule.eq_top_of_isLocalized'_span {N : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ ↦ by simp only [h, Submodule.localized'_top]

end span
