/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a Noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a Noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

-/


variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

open LinearMap

/-- `IsAssociatedPrime I M` if the prime ideal `I` is the annihilator of some `x : M`. -/
def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x : M, I = ker (toSpanSingleton R M x)

theorem isAssociatedPrime_iff_exists_injective_linearMap :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ (f : R ⧸ I →ₗ[R] M), Function.Injective f := by
  rw [IsAssociatedPrime]
  congr! 1
  refine ⟨fun ⟨_, h⟩ ↦ ⟨Submodule.liftQ _ _ h.le, ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot' _ _ h)⟩,
    fun ⟨f, h⟩ ↦ ⟨(f ∘ₗ Submodule.mkQ I) 1, ?_⟩⟩
  have := I.ker_mkQ ▸ ker_comp_of_ker_eq_bot (Submodule.mkQ I) (ker_eq_bot_of_injective h)
  convert this.symm using 2
  ext; simp

variable (R)

/-- The set of associated primes of a module. -/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M R}
variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

theorem AssociatePrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl

theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1
theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  simp_rw [mem_ker, toSpanSingleton_apply, ← map_smul, ← f.map_zero, hf.eq_iff]

theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩

theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M := by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  simpa [Subsingleton.elim x 0] using hx

variable (R) in
theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x ≠ 0) : ∃ P : Ideal R, IsAssociatedPrime P M ∧ ker (toSpanSingleton R M x) ≤ P := by
  have : ker (toSpanSingleton R M x) ≠ ⊤ := by
    rwa [Ne, Ideal.eq_top_iff_one, mem_ker, toSpanSingleton_apply, one_smul]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | ker (toSpanSingleton R M x) ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = ker (toSpanSingleton R M y) }
      ⟨_, rfl.le, this, x, rfl⟩
  refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  intro a b hab
  rw [or_iff_not_imp_left]
  intro ha
  rw [mem_ker, toSpanSingleton_apply] at ha hab
  have H₁ : ker (toSpanSingleton R M y) ≤ ker (toSpanSingleton R M (a • y)) := by
    intro c hc
    rw [mem_ker, toSpanSingleton_apply] at hc ⊢
    rw [smul_comm, hc, smul_zero]
  have H₂ : ker (toSpanSingleton R M (a • y)) ≠ ⊤ := by
    rwa [Ne, ker_eq_top, toSpanSingleton_eq_zero_iff]
  rwa [H₁.eq_of_not_lt (h₃ _ ⟨l.trans H₁, H₂, _, rfl⟩),
    mem_ker, toSpanSingleton_apply, smul_comm, smul_smul]

namespace associatedPrimes

variable {f} {M'' : Type*} [AddCommGroup M''] [Module R M''] {g : M' →ₗ[R] M''}

/-- If `M → M'` is injective, then the set of associated primes of `M` is
contained in that of `M'`. -/
@[stacks 02M3 "first part"]
theorem subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M ⊆ associatedPrimes R M' := fun _I h => h.map_of_injective f hf

/-- If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of `M'` is
contained in the union of those of `M` and `M''`. -/
@[stacks 02M3 "second part"]
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∪ associatedPrimes R M'' := by
  rintro p ⟨_, x, hx⟩
  by_cases h : ∃ a ∈ p.primeCompl, ∃ y : M, f y = a • x
  · obtain ⟨a, ha, y, h⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb ⊢
      apply_fun _ using hf
      rw [map_smul, map_zero, h, smul_comm, hb, smul_zero]
    · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb
      apply_fun f at hb
      rw [map_smul, map_zero, h, ← mul_smul, ← LinearMap.toSpanSingleton_apply,
        ← LinearMap.mem_ker, ← hx] at hb
      contrapose! hb
      exact p.primeCompl.mul_mem hb ha
  · push_neg at h
    right
    refine ⟨‹_›, g x, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb ⊢
      rw [← map_smul, hb, map_zero]
    · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra! H
      exact h b H y hy

variable (R M M') in
/-- The set of associated primes of the product of two modules is equal to
the union of those of the two modules. -/
@[stacks 02M3 "third part"]
theorem prod : associatedPrimes R (M × M') = associatedPrimes R M ∪ associatedPrimes R M' :=
  (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm (Set.union_subset_iff.2
    ⟨subset_of_injective LinearMap.inl_injective, subset_of_injective LinearMap.inr_injective⟩)

end associatedPrimes

theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l.injective)
    (associatedPrimes.subset_of_injective l.symm.injective)

theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

variable (R M)

theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩

theorem biUnion_associatedPrimes_eq_zero_divisors [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R M, p = { r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0 } := by
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    refine ⟨x, ne_of_eq_of_ne (one_smul R x).symm ?_, h'⟩
    exact (Ideal.ne_top_iff_one _).mp h.ne_top
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h
    exact Set.mem_biUnion hP (hx h')

variable {R M}

theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I := by
  obtain ⟨hI, x, rfl⟩ := h
  rw [← Submodule.annihilator_span_singleton]
  exact Submodule.annihilator_mono le_top

theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  have : x ≠ 0 := by
    rintro rfl
    apply hJ.1
    rwa [toSpanSingleton_zero, ker_zero] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  replace e : ∀ {y}, y ∈ J ↔ x * y ∈ I := by
    intro y
    rw [e, mem_ker, toSpanSingleton_apply, ← map_smul, smul_eq_mul, mul_comm,
      Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero]
  apply le_antisymm
  · intro y hy
    exact ((Ideal.isPrimary_iff.1 hI).2 <| e.mp hy).resolve_left
      ((Submodule.Quotient.mk_eq_zero I).not.mp this)
  · rw [hJ.radical_le_iff]
    intro y hy
    exact e.mpr (I.mul_mem_left x hy)

theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} := by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I :) 1, (Ideal.Quotient.mk I :) 0, ?_⟩
    rw [Ne, Ideal.Quotient.eq, sub_zero, ← Ideal.eq_top_iff_one]
    exact hI.1
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
