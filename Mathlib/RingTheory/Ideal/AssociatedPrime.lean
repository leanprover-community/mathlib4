/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Span
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Noetherian

#align_import ring_theory.ideal.associated_prime from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## Todo

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

-/


variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- `IsAssociatedPrime I M` if the prime ideal `I` is the annihilator of some `x : M`. -/
def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x : M, I = (R ∙ x).annihilator
#align is_associated_prime IsAssociatedPrime

variable (R)

/-- The set of associated primes of a module. -/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }
#align associated_primes associatedPrimes

variable {I J M R}

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

theorem AssociatePrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl
#align associate_primes.mem_iff AssociatePrimes.mem_iff

theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1
#align is_associated_prime.is_prime IsAssociatedPrime.isPrime
theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  -- ⊢ IsAssociatedPrime (Submodule.annihilator (Submodule.span R {x})) M'
  refine' ⟨h.1, ⟨f x, _⟩⟩
  -- ⊢ Submodule.annihilator (Submodule.span R {x}) = Submodule.annihilator (Submod …
  ext r
  -- ⊢ r ∈ Submodule.annihilator (Submodule.span R {x}) ↔ r ∈ Submodule.annihilator …
  rw [Submodule.mem_annihilator_span_singleton, Submodule.mem_annihilator_span_singleton, ←
    map_smul, ← f.map_zero, hf.eq_iff]
#align is_associated_prime.map_of_injective IsAssociatedPrime.map_of_injective

theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩
#align linear_equiv.is_associated_prime_iff LinearEquiv.isAssociatedPrime_iff

theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M := by
  rintro ⟨hI, x, hx⟩
  -- ⊢ False
  apply hI.ne_top
  -- ⊢ I = ⊤
  rwa [Subsingleton.elim x 0, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.annihilator_bot]
    at hx
#align not_is_associated_prime_of_subsingleton not_isAssociatedPrime_of_subsingleton

variable (R)

theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x ≠ 0) : ∃ P : Ideal R, IsAssociatedPrime P M ∧ (R ∙ x).annihilator ≤ P := by
  have : (R ∙ x).annihilator ≠ ⊤ := by
    rwa [Ne.def, Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (R ∙ x).annihilator ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = (R ∙ y).annihilator }
      ⟨(R ∙ x).annihilator, rfl.le, this, x, rfl⟩
  refine' ⟨_, ⟨⟨h₁, _⟩, y, rfl⟩, l⟩
  -- ⊢ ∀ {x y_1 : R}, x * y_1 ∈ Submodule.annihilator (Submodule.span R {y}) → x ∈  …
  intro a b hab
  -- ⊢ a ∈ Submodule.annihilator (Submodule.span R {y}) ∨ b ∈ Submodule.annihilator …
  rw [or_iff_not_imp_left]
  -- ⊢ ¬a ∈ Submodule.annihilator (Submodule.span R {y}) → b ∈ Submodule.annihilato …
  intro ha
  -- ⊢ b ∈ Submodule.annihilator (Submodule.span R {y})
  rw [Submodule.mem_annihilator_span_singleton] at ha hab
  -- ⊢ b ∈ Submodule.annihilator (Submodule.span R {y})
  have H₁ : (R ∙ y).annihilator ≤ (R ∙ a • y).annihilator := by
    intro c hc
    rw [Submodule.mem_annihilator_span_singleton] at hc ⊢
    rw [smul_comm, hc, smul_zero]
  have H₂ : (Submodule.span R {a • y}).annihilator ≠ ⊤ := by
    rwa [Ne.def, Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot]
  rwa [H₁.eq_of_not_lt (h₃ (R ∙ a • y).annihilator ⟨l.trans H₁, H₂, _, rfl⟩),
    Submodule.mem_annihilator_span_singleton, smul_comm, smul_smul]
#align exists_le_is_associated_prime_of_is_noetherian_ring exists_le_isAssociatedPrime_of_isNoetherianRing

variable {R}

theorem associatedPrimes.subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M ⊆ associatedPrimes R M' := fun _I h => h.map_of_injective f hf
#align associated_primes.subset_of_injective associatedPrimes.subset_of_injective

theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l l.injective)
    (associatedPrimes.subset_of_injective l.symm l.symm.injective)
#align linear_equiv.associated_primes.eq LinearEquiv.AssociatedPrimes.eq

theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false_iff];
  -- ⊢ x✝ ∈ associatedPrimes R M ↔ x✝ ∈ ∅
       -- ⊢ ¬x✝ ∈ associatedPrimes R M
  apply not_isAssociatedPrime_of_subsingleton
  -- 🎉 no goals
#align associated_primes.eq_empty_of_subsingleton associatedPrimes.eq_empty_of_subsingleton

variable (R M)

theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  -- ⊢ Set.Nonempty (associatedPrimes R M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  -- ⊢ Set.Nonempty (associatedPrimes R M)
  exact ⟨P, hP⟩
  -- 🎉 no goals
#align associated_primes.nonempty associatedPrimes.nonempty

variable {R M}

theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I := by
  obtain ⟨hI, x, rfl⟩ := h
  -- ⊢ Submodule.annihilator ⊤ ≤ Submodule.annihilator (Submodule.span R {x})
  exact Submodule.annihilator_mono le_top
  -- 🎉 no goals
#align is_associated_prime.annihilator_le IsAssociatedPrime.annihilator_le

theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  -- ⊢ J = Ideal.radical I
  have : x ≠ 0 := by
    rintro rfl
    apply hJ.1
    rwa [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.annihilator_bot] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  -- ⊢ J = Ideal.radical I
  replace e : ∀ {y}, y ∈ J ↔ x * y ∈ I
  -- ⊢ ∀ {y : R}, y ∈ J ↔ x * y ∈ I
  · intro y
    -- ⊢ y ∈ J ↔ x * y ∈ I
    rw [e, Submodule.mem_annihilator_span_singleton, ← map_smul, smul_eq_mul, mul_comm,
      Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero]
  apply le_antisymm
  -- ⊢ J ≤ Ideal.radical I
  · intro y hy
    -- ⊢ y ∈ Ideal.radical I
    exact (hI.2 <| e.mp hy).resolve_left ((Submodule.Quotient.mk_eq_zero I).not.mp this)
    -- 🎉 no goals
  · rw [hJ.radical_le_iff]
    -- ⊢ I ≤ J
    intro y hy
    -- ⊢ y ∈ J
    exact e.mpr (I.mul_mem_left x hy)
    -- 🎉 no goals
#align is_associated_prime.eq_radical IsAssociatedPrime.eq_radical

theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} := by
  ext J
  -- ⊢ J ∈ associatedPrimes R (R ⧸ I) ↔ J ∈ {Ideal.radical I}
  rw [Set.mem_singleton_iff]
  -- ⊢ J ∈ associatedPrimes R (R ⧸ I) ↔ J = Ideal.radical I
  refine' ⟨IsAssociatedPrime.eq_radical hI, _⟩
  -- ⊢ J = Ideal.radical I → J ∈ associatedPrimes R (R ⧸ I)
  rintro rfl
  -- ⊢ Ideal.radical I ∈ associatedPrimes R (R ⧸ I)
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I : _) 1, (Ideal.Quotient.mk I : _) 0, ?_⟩
    rw [Ne.def, Ideal.Quotient.eq, sub_zero, ← Ideal.eq_top_iff_one]
    exact hI.1
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  -- ⊢ Ideal.radical I ∈ associatedPrimes R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
  -- 🎉 no goals
#align associated_primes.eq_singleton_of_is_primary associatedPrimes.eq_singleton_of_isPrimary
