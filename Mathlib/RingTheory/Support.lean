/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# Support of a module

## Main results
- `Module.support`: The support of an `R`-module as a subset of `Spec R`.
- `Module.mem_support_iff_exists_annihilator`: `p ∈ Supp M ↔ ∃ m, Ann(m) ≤ p`.
- `Module.support_eq_empty_iff`: `Supp M = ∅ ↔ M = 0`
- `Module.support_of_exact`: `Supp N = Supp M ∪ Supp P` for an exact sequence `0 → M → N → P → 0`.
- `Module.support_eq_zeroLocus`: If `M` is `R`-finite, then `Supp M = Z(Ann(M))`.
- `LocalizedModule.exists_subsingleton_away`:
  If `M` is `R`-finite and `Mₚ = 0`, then `M[1/f] = 0` for some `p ∈ D(f)`.

Also see `Mathlib/RingTheory/Spectrum/Prime/Module.lean` for other results
depending on the Zariski topology.

## TODO
- Connect to associated primes once we have them in mathlib.
- Given an `R`-algebra `f : R → A` and a finite `R`-module `M`,
  `Supp_A (A ⊗ M) = f♯ ⁻¹ Supp M` where `f♯ : Spec A → Spec R`. (stacks#0BUR)
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

-- Basic files in `RingTheory` should avoid depending on the Zariski topology
-- See `Mathlib/RingTheory/Spectrum/Prime/Module.lean`
assert_not_exists TopologicalSpace

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}

variable (R M) in
/-- The support of a module, defined as the set of primes `p` such that `Mₚ ≠ 0`. -/
@[stacks 00L1]
def Module.support : Set (PrimeSpectrum R) :=
  { p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }

lemma Module.mem_support_iff :
    p ∈ Module.support R M ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := Iff.rfl

lemma Module.notMem_support_iff :
    p ∉ Module.support R M ↔ Subsingleton (LocalizedModule p.asIdeal.primeCompl M) :=
  not_nontrivial_iff_subsingleton

lemma Module.notMem_support_iff' :
    p ∉ Module.support R M ↔ ∀ m : M, ∃ r ∉ p.asIdeal, r • m = 0 := by
  simp only [notMem_support_iff, Ideal.primeCompl, LocalizedModule.subsingleton_iff,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]

lemma Module.mem_support_iff' :
    p ∈ Module.support R M ↔ ∃ m : M, ∀ r ∉ p.asIdeal, r • m ≠ 0 := by
  rw [← @not_not (_ ∈ _), notMem_support_iff']
  push Not
  rfl

lemma Module.mem_support_iff_exists_annihilator :
    p ∈ Module.support R M ↔ ∃ m : M, (R ∙ m).annihilator ≤ p.asIdeal := by
  rw [Module.mem_support_iff']
  simp_rw [not_imp_not, SetLike.le_def, Submodule.mem_annihilator_span_singleton]

lemma Module.mem_support_mono {p q : PrimeSpectrum R} (H : p ≤ q) (hp : p ∈ Module.support R M) :
    q ∈ Module.support R M := by
  rw [Module.mem_support_iff_exists_annihilator] at hp ⊢
  exact ⟨_, hp.choose_spec.trans H⟩

lemma Module.mem_support_iff_of_span_eq_top {s : Set M} (hs : Submodule.span R s = ⊤) :
    p ∈ Module.support R M ↔ ∃ m ∈ s, (R ∙ m).annihilator ≤ p.asIdeal := by
  constructor
  · contrapose
    rw [notMem_support_iff, LocalizedModule.subsingleton_iff_ker_eq_top, ← top_le_iff,
      ← hs, Submodule.span_le, Set.subset_def]
    simp_rw [SetLike.le_def, Submodule.mem_annihilator_span_singleton, SetLike.mem_coe,
      LocalizedModule.mem_ker_mkLinearMap_iff]
    push Not
    simp_rw [and_comm]
    exact id
  · intro ⟨m, _, hm⟩
    exact mem_support_iff_exists_annihilator.mpr ⟨m, hm⟩

lemma Module.annihilator_le_of_mem_support (hp : p ∈ Module.support R M) :
    Module.annihilator R M ≤ p.asIdeal := by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
  exact le_trans ((Submodule.subtype _).annihilator_le_of_injective Subtype.val_injective) hm

lemma LocalizedModule.subsingleton_iff_support_subset {f : R} :
    Subsingleton (LocalizedModule (.powers f) M) ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus {f} := by
  rw [LocalizedModule.subsingleton_iff]
  constructor
  · rintro H x hx' f rfl
    obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hx'
    obtain ⟨_, ⟨n, rfl⟩, e⟩ := H m
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n
      (hm ((Submodule.mem_annihilator_span_singleton _ _).mpr e))
  · intro H m
    by_cases h : (Submodule.span R {m}).annihilator = ⊤
    · rw [Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot] at h
      exact ⟨1, one_mem _, by simpa using h⟩
    obtain ⟨n, hn⟩ : f ∈ (Submodule.span R {m}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro p ⟨hp, hp'⟩
      simpa using H (Module.mem_support_iff_exists_annihilator (p := ⟨p, hp'⟩).mpr ⟨_, hp⟩)
    exact ⟨_, ⟨n, rfl⟩, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩

lemma Module.support_eq_empty_iff :
    Module.support R M = ∅ ↔ Subsingleton M := by
  rw [← Set.subset_empty_iff, ← PrimeSpectrum.zeroLocus_singleton_one,
    ← LocalizedModule.subsingleton_iff_support_subset, LocalizedModule.subsingleton_iff,
    subsingleton_iff_forall_eq 0]
  simp only [Submonoid.powers_one, Submonoid.mem_bot, exists_eq_left, one_smul]

lemma Module.nonempty_support_iff :
    (Module.support R M).Nonempty ↔ Nontrivial M := by
  rw [Set.nonempty_iff_ne_empty, ne_eq,
    Module.support_eq_empty_iff, ← not_subsingleton_iff_nontrivial]

lemma Module.nonempty_support_of_nontrivial [Nontrivial M] : (Module.support R M).Nonempty :=
  Module.nonempty_support_iff.mpr ‹_›

lemma Module.support_eq_empty [Subsingleton M] :
    Module.support R M = ∅ :=
  Module.support_eq_empty_iff.mpr ‹_›

lemma Module.support_of_algebra {A : Type*} [Ring A] [Algebra R A] :
    Module.support R A = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R A)) := by
  ext p
  simp only [mem_support_iff', ne_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun ⟨m, hm⟩ x hx ↦ not_not.mp fun hx' ↦ ?_, fun H ↦ ⟨1, fun r hr e ↦ ?_⟩⟩
  · simpa [Algebra.smul_def, (show _ = _ from hx)] using hm _ hx'
  · exact hr (H ((Algebra.algebraMap_eq_smul_one _).trans e))

lemma Module.support_of_noZeroSMulDivisors [IsDomain R] [IsTorsionFree R M] [Nontrivial M] :
    Module.support R M = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_support_iff', ne_eq, smul_eq_zero, not_or]
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact fun p ↦ ⟨x, fun r hr ↦ ⟨fun e ↦ hr (e ▸ p.asIdeal.zero_mem), hx⟩⟩

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (f : M →ₗ[R] N) (g : N →ₗ[R] P)

@[stacks 00L3 "(2)"]
lemma Module.support_subset_of_injective (hf : Function.Injective f) :
    Module.support R M ⊆ Module.support R N := by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  exact ⟨f m, fun r hr ↦ by simpa using hf.ne (hm r hr)⟩

@[stacks 00L3 "(3)"]
lemma Module.support_subset_of_surjective (hf : Function.Surjective f) :
    Module.support R N ⊆ Module.support R M := by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  obtain ⟨m, rfl⟩ := hf m
  exact ⟨m, fun r hr e ↦ hm r hr (by simpa using congr(f $e))⟩

variable {f g} in
/-- Given an exact sequence `0 → M → N → P → 0` of `R`-modules, `Supp N = Supp M ∪ Supp P`. -/
@[stacks 00L3 "(4)"]
lemma Module.support_of_exact (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.support R N = Module.support R M ∪ Module.support R P := by
  refine subset_antisymm ?_ (Set.union_subset (Module.support_subset_of_injective f hf)
    (Module.support_subset_of_surjective g hg))
  intro x
  contrapose
  simp only [Set.mem_union, not_or, and_imp, notMem_support_iff']
  intro H₁ H₂ m
  obtain ⟨r, hr, e₁⟩ := H₂ (g m)
  rw [← map_smul, h] at e₁
  obtain ⟨m', hm'⟩ := e₁
  obtain ⟨s, hs, e₁⟩ := H₁ m'
  exact ⟨_, x.asIdeal.primeCompl.mul_mem hs hr, by rw [mul_smul, ← hm', ← map_smul, e₁, map_zero]⟩

lemma LinearEquiv.support_eq (e : M ≃ₗ[R] N) :
    Module.support R M = Module.support R N :=
  (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
    (Module.support_subset_of_surjective e.toLinearMap e.surjective)

section Finite

variable [Module.Finite R M]

open PrimeSpectrum

lemma Module.mem_support_iff_of_finite :
    p ∈ Module.support R M ↔ Module.annihilator R M ≤ p.asIdeal := by
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  refine ⟨annihilator_le_of_mem_support, fun H ↦ (mem_support_iff_of_span_eq_top hs).mpr ?_⟩
  simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton] at H ⊢
  contrapose! H
  choose x hx hx' using Subtype.forall'.mp H
  refine ⟨s.attach.prod x, ?_, ?_⟩
  · rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    intro m
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem x (Finset.mem_attach _ m)
    rw [hk, mul_comm, mul_smul, hx, smul_zero]
  · exact p.asIdeal.primeCompl.prod_mem (fun x _ ↦ hx' x)

/-- If `M` is `R`-finite, then `Supp M = Z(Ann(M))`. -/
@[stacks 00L2]
lemma Module.support_eq_zeroLocus :
    Module.support R M = zeroLocus (Module.annihilator R M) :=
  Set.ext fun _ ↦ mem_support_iff_of_finite

/-- If `M` is a finite module such that `Mₚ = 0` for some `p`,
then `M[1/f] = 0` for some `p ∈ D(f)`. -/
lemma LocalizedModule.exists_subsingleton_away (p : Ideal R) [p.IsPrime]
    [Subsingleton (LocalizedModule p.primeCompl M)] :
    ∃ f ∉ p, Subsingleton (LocalizedModule (.powers f) M) := by
  have : ⟨p, inferInstance⟩ ∈ (Module.support R M)ᶜ := by
    simpa [Module.notMem_support_iff]
  rw [Module.support_eq_zeroLocus, ← Set.biUnion_of_singleton (Module.annihilator R M : Set R),
    PrimeSpectrum.zeroLocus_iUnion₂, Set.compl_iInter₂, Set.mem_iUnion₂] at this
  obtain ⟨f, hf, hf'⟩ := this
  exact ⟨f, by simpa using hf', subsingleton_iff.mpr
    fun m ↦ ⟨f, Submonoid.mem_powers f, Module.mem_annihilator.mp hf _⟩⟩

lemma IsLocalizedModule.exists_subsingleton_away {M' : Type*} [AddCommMonoid M'] [Module R M']
    (l : M →ₗ[R] M') (p : Ideal R) [p.IsPrime] [IsLocalizedModule p.primeCompl l]
    [Subsingleton M'] :
    ∃ f ∉ p, Subsingleton (LocalizedModule (.powers f) M) := by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  exact LocalizedModule.exists_subsingleton_away p

/-- `Supp(M/IM) = Supp(M) ∩ Z(I)`. -/
@[stacks 00L3 "(1)"]
theorem Module.support_quotient (I : Ideal R) :
    support R (M ⧸ (I • ⊤ : Submodule R M)) = support R M ∩ zeroLocus I := by
  apply subset_antisymm
  · refine Set.subset_inter ?_ ?_
    · exact Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)
    · rw [support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono_ideal
      rw [Submodule.annihilator_quotient]
      exact fun x hx ↦ Submodule.mem_colon.mpr fun p hp ↦ Submodule.smul_mem_smul hx hp
  · rintro p ⟨hp₁, hp₂⟩
    rw [Module.mem_support_iff] at hp₁ ⊢
    let Rₚ := Localization.AtPrime p.asIdeal
    let Mₚ := LocalizedModule p.asIdeal.primeCompl M
    set Mₚ' := LocalizedModule p.asIdeal.primeCompl (M ⧸ (I • ⊤ : Submodule R M))
    let Mₚ'' := Mₚ ⧸ I.map (algebraMap R Rₚ) • (⊤ : Submodule Rₚ Mₚ)
    let e : Mₚ' ≃ₗ[Rₚ] Mₚ'' := (localizedQuotientEquiv _ _).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by rw [Submodule.localized,
        Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top])
    have : Nontrivial Mₚ'' := by
      rw [Submodule.Quotient.nontrivial_iff, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine trans ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hp₂
    exact e.nontrivial

open Pointwise in
@[simp]
theorem Module.support_quotSMulTop (x : R) :
    support R (QuotSMulTop x M) = support R M ∩ zeroLocus {x} :=
  (x • (⊤ : Submodule R M)).quotEquivOfEq (Ideal.span {x} • ⊤)
    ((⊤ : Submodule R M).ideal_span_singleton_smul x).symm |>.support_eq.trans <|
      (support_quotient _).trans <| by rw [zeroLocus_span]

end Finite
