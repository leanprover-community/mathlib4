/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Away.Basic

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

theorem Submodule.eq_top_of_localization_maximal (N₁ : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) = ⊤) :
    N₁ = ⊤ :=
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

section localization_maximal

open Submodule LocalizedModule Ideal LinearMap

/-- Another version, using `LocalizedModule` instead of `IsLocalizedModule`. -/
lemma Submodule.le_of_localization_maximal' {N H : Submodule R M}
    (h : ∀ (J : Ideal R) [J.IsMaximal], localized J.primeCompl N ≤ localized J.primeCompl H) :
    N ≤ H := Submodule.le_of_localization_maximal (fun P ↦ (Localization P.primeCompl))
    (fun P ↦ (LocalizedModule P.primeCompl M))
    (fun P ↦ (mkLinearMap P.primeCompl M)) (fun P _ ↦ h P)

/-- Another version, using `LocalizedModule` instead of `IsLocalizedModule`. -/
lemma Submodule.eq_of_localization_maximal' {N P : Submodule R M}
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), localized J.primeCompl N = localized J.primeCompl P) :
    N = P :=
  eq_of_le_of_le (le_of_localization_maximal' (fun J hJ ↦ le_of_eq (h J hJ)))
  (le_of_localization_maximal' (fun J hJ ↦ le_of_eq (h J hJ).symm))

/-- Another version, using `LocalizedModule` instead of `IsLocalizedModule`. -/
lemma Submodule.eq_bot_of_localization_maximal' {N : Submodule R M}
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), localized J.primeCompl N = ⊥) :
  N = ⊥ := eq_of_localization_maximal' fun _ _ ↦ by simp only [h, localized'_bot]

/-- Another version, using `LocalizedModule` instead of `IsLocalizedModule`. -/
lemma Submodule.eq_top_of_localization_maximal' {N : Submodule R M}
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), localized J.primeCompl N = ⊤) :
  N = ⊤ := eq_of_localization_maximal' fun _ _ ↦ by simp only [h, localized'_top]

end localization_maximal

section span

open IsLocalizedModule LocalizedModule Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (s : Set R) (spn : Ideal.span s = ⊤)
include spn

theorem eq_zero_of_localization_span (x : M)
    (h : ∀ r : s, (mkLinearMap (Submonoid.powers r.1) M ) x = 0) : x = 0 := by
  rw [← Submodule.span_singleton_eq_bot (R := R), ← Submodule.annihilator_eq_top_iff]
  by_contra! H
  obtain ⟨m, maxm, lem⟩ := exists_le_maximal _ H
  have exr : ∃ r : s, r.1 ∉ m := by
    by_contra! H
    exact maxm.ne_top (top_le_iff.mp (spn ▸ (Ideal.span_le.mpr (Subtype.forall.mp H))))
  obtain ⟨r, nm⟩ := exr
  obtain ⟨s, hs⟩ := (mk'_eq_zero' _ _ ).mp ((mk_eq_mk' (1 : Submonoid.powers r.1) x)
    ▸ (mkLinearMap_apply (Submonoid.powers r.1) M x) ▸ (h r))
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  exact nm (maxm.isPrime.mem_of_pow_mem n
    (lem ((Submodule.mem_annihilator_span_singleton x (r.1 ^ n)).mpr (hn ▸ hs))))

theorem Submodule.le_of_localization_span {N P : Submodule R M}
    (h : ∀ r : s, N.localized (Submonoid.powers r.1) ≤ P.localized (Submonoid.powers r.1)) :
      N ≤ P := by
  by_contra nle
  obtain ⟨n, hn, hp⟩ := Set.not_subset.mp nle
  set I := P.colon (Submodule.span R {n})
  obtain ⟨m ,maxm, lem⟩ := exists_le_maximal _ ((ne_top_iff_one _).mpr
    fun H ↦ (one_smul R n ▸ hp) (Submodule.mem_colon_singleton.mp H))
  have exr : ∃ r : s, r.1 ∉ m := by
    by_contra! H
    exact maxm.ne_top (top_le_iff.mp (spn ▸ (Ideal.span_le.mpr (Subtype.forall.mp H))))
  obtain ⟨r, nm⟩ := exr
  have mem : (mkLinearMap (Submonoid.powers r.1) M) n ∈ N.localized (Submonoid.powers r.1) := by
    simp only [mkLinearMap_apply, Submodule.mem_localized']
    exact ⟨n, hn, 1, by rw [mk'_one, mkLinearMap_apply]⟩
  apply (h r) at mem
  simp only [mkLinearMap_apply, Submodule.mem_localized', mk_eq_mk'] at mem
  obtain ⟨p, inp, s, hs⟩ := mem
  obtain ⟨s', eq⟩ := (mk'_eq_mk'_iff _ p n s 1).mp hs
  simp only [one_smul, smul_smul] at eq
  have h1 : (s' * s).1 ∈ I := by
    have : (s'.1 * s.1) • n = (s' * s) • n := rfl
    rw [Submonoid.coe_mul, Submodule.mem_colon_singleton, this, eq]
    exact P.smul_mem ((Submonoid.powers r.1).subtype s') inp
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (s' * s).2
  exact nm (maxm.isPrime.mem_of_pow_mem k (hk ▸ (lem h1)))

theorem Submodule.eq_of_localization_span {N P : Submodule R M}
    (h : ∀ r : s, N.localized (Submonoid.powers r.1) = P.localized (Submonoid.powers r.1)) :
    N = P :=
  eq_of_le_of_le (le_of_localization_span s spn (fun r ↦ le_of_eq (h r)))
  (le_of_localization_span s spn (fun r ↦ le_of_eq (h r).symm))

theorem Submodule.eq_bot_of_localization_span {N : Submodule R M}
    (h : ∀ r : s, N.localized (Submonoid.powers r.1)= ⊥) : N = ⊥ :=
  eq_of_localization_span _ spn fun _ ↦ by simp only [h, Submodule.localized'_bot]

theorem Submodule.eq_top_of_localization_span {N : Submodule R M}
    (h : ∀ r : s, N.localized (Submonoid.powers r.1) = ⊤) : N = ⊤ :=
  eq_of_localization_span _ spn fun _ ↦ by simp only [h, Submodule.localized'_top]

end span

section span'

open IsLocalizedModule LocalizedModule Ideal

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] (s : Set R) (spn : Ideal.span s = ⊤)
include spn

variable
  (Rₚ : ∀ _ : s, Type*)
  [∀ r : s, CommRing (Rₚ r)]
  [∀ r : s, Algebra R (Rₚ r)]
  [∀ r : s, IsLocalization.Away r.1 (Rₚ r)]
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  [∀ r : s, Module (Rₚ r) (Mₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (f r)]

theorem eq_zero_of_localization_span' (x : M)
    (h : ∀ r : s, f r x = 0) : x = 0 := by
  rw [← Submodule.span_singleton_eq_bot (R := R), ← Submodule.annihilator_eq_top_iff]
  by_contra! H
  obtain ⟨m, maxm, lem⟩ := exists_le_maximal _ H
  have exr : ∃ r : s, r.1 ∉ m := by
    by_contra! H
    exact maxm.ne_top (top_le_iff.mp (spn ▸ (Ideal.span_le.mpr (Subtype.forall.mp H))))
  obtain ⟨r, nm⟩ := exr
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers r.1) (f r)).mp <| h r
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
  exact nm (maxm.isPrime.mem_of_pow_mem n
    (lem ((Submodule.mem_annihilator_span_singleton x (r.1 ^ n)).mpr (hn ▸ ht))))

theorem Submodule.le_of_localization_span' {N P : Submodule R M} (h : ∀ r : s,
    N.localized' (Rₚ r) (Submonoid.powers r.1) (f r) ≤
    P.localized' (Rₚ r) (Submonoid.powers r.1) (f r)) : N ≤ P := by
  by_contra nle
  obtain ⟨n, hn, hp⟩ := Set.not_subset.mp nle
  set I := P.colon (Submodule.span R {n})
  obtain ⟨m ,maxm, lem⟩ := exists_le_maximal _ ((ne_top_iff_one _).mpr
    fun H ↦ (one_smul R n ▸ hp) (Submodule.mem_colon_singleton.mp H))
  have exr : ∃ r : s, r.1 ∉ m := by
    by_contra! H
    exact maxm.ne_top (top_le_iff.mp (spn ▸ (Ideal.span_le.mpr (Subtype.forall.mp H))))
  obtain ⟨r, nm⟩ := exr
  have mem : (f r) n ∈ N.localized' (Rₚ r) (Submonoid.powers r.1) (f r) := (mem_localized'
    (Rₚ r) _ (f r) N ((f r) n)).mpr ⟨n, hn, 1, mk'_one _ (f r) n⟩
  apply (h r) at mem
  simp only [mkLinearMap_apply, Submodule.mem_localized', mk_eq_mk'] at mem
  obtain ⟨p, inp, s, hs⟩ := mem
  rw [← mk'_one (Submonoid.powers r.1) (f r) n] at hs
  obtain ⟨s', eq⟩ := (mk'_eq_mk'_iff _ p n s 1).mp hs
  simp only [one_smul, smul_smul] at eq
  have h1 : (s' * s).1 ∈ I := by
    have : (s'.1 * s.1) • n = (s' * s) • n := rfl
    rw [Submonoid.coe_mul, Submodule.mem_colon_singleton, this, eq]
    exact P.smul_mem ((Submonoid.powers r.1).subtype s') inp
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (s' * s).2
  exact nm (maxm.isPrime.mem_of_pow_mem k (hk ▸ (lem h1)))

theorem Submodule.eq_of_localization_span' {N P : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (Submonoid.powers r.1) (f r) =
    P.localized' (Rₚ r) (Submonoid.powers r.1) (f r)) : N = P :=
  eq_of_le_of_le (le_of_localization_span' s spn _ _ _ (fun r ↦ le_of_eq (h r)))
  (le_of_localization_span' s spn _ _ _ (fun r ↦ le_of_eq (h r).symm))

theorem Submodule.eq_bot_of_localization_span' {N : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (Submonoid.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_localization_span' s spn Rₚ Mₚ f fun _ ↦ by simp only [h, Submodule.localized'_bot]

theorem Submodule.eq_top_of_localization_span' {N : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (Submonoid.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_localization_span' s spn Rₚ Mₚ f fun _ ↦ by simp only [h, Submodule.localized'_top]

end span'
