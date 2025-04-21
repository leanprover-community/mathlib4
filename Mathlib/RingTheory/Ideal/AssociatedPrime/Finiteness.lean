/-
Copyright (c) 2025 Jinzhao Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Pan
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!

# Finitely generated module over noetherian ring have finitely many associated primes.

In this file we proved that any finitely generated module over a noetherian ring have finitely many
associated primes.

## Main results

* `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`: If `A` is a Noetherian ring
  and `M` is a finitely generated `A`-module, then there exists a chain of submodules
  `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
  `Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`.

* `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`: If a property on
  finitely generated modules over a Noetherian ring satisfies that:

  - it holds for zero module,
  - it holds for any module isomorphic to some `A ⧸ p` where `p` is a prime ideal of `A`,
  - it is stable by short exact sequences,

  then the property holds for every finitely generated modules.

* `associatedPrimes.finite`: There are only finitely many associated primes of a
  finitely generated module over a Noetherian ring.

-/

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] {n : ℕ} {N : Submodule A M}

section

omit [Module.Finite A M]

/-- A `Prop` asserting that two submodules `N₁, N₂` satisfy `N₁ ≤ N₂` and
`N₂ / N₁` is isomorphic to `A / p` for some prime ideal `p` of `A`. -/
def Submodule.IsQuotientEquivQuotientPrime (N₁ N₂ : Submodule A M) :=
  N₁ ≤ N₂ ∧ ∃ (p : PrimeSpectrum A), Nonempty ((↥N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[A] A ⧸ p.1)

private theorem aux (h : N ≠ ⊤) :
    ∃ (p : PrimeSpectrum A) (f : A ⧸ p.1 →ₗ[A] M ⧸ N), Function.Injective f := by
  have := Submodule.Quotient.nontrivial_of_lt_top _ h.lt_top
  have h := (associatedPrimes.nonempty A (M ⧸ N)).some_mem
  rw [AssociatePrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at h
  exact ⟨⟨_, h.1⟩, h.2⟩

private noncomputable def auxP (h : N ≠ ⊤) : PrimeSpectrum A := (aux h).choose

private noncomputable def auxLinearMap (h : N ≠ ⊤) :
    A ⧸ (auxP h).1 →ₗ[A] M ⧸ N := (aux h).choose_spec.choose

private theorem auxLinearMap_injective (h : N ≠ ⊤) : Function.Injective (auxLinearMap h) :=
  (aux h).choose_spec.choose_spec

private noncomputable def auxSeq
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] : ℕ → Submodule A M
  | 0 => ⊥
  | n + 1 =>
    open scoped Classical in
    if h : auxSeq A M n = ⊤ then
      ⊤
    else
      (LinearMap.range (auxLinearMap h)).comap (auxSeq A M n).mkQ

variable (A M) in
private theorem auxSeq_zero : auxSeq A M 0 = ⊥ := rfl

private theorem auxSeq_succ_of_eq_top (h : auxSeq A M n = ⊤) : auxSeq A M (n + 1) = ⊤ := by
  simp only [auxSeq, dif_pos h]

private theorem auxSeq_succ_of_ne_top (h : auxSeq A M n ≠ ⊤) :
    auxSeq A M (n + 1) = (LinearMap.range (auxLinearMap h)).comap (auxSeq A M n).mkQ := by
  simp only [auxSeq, dif_neg h]

private theorem lt_auxSeq_succ_of_ne_top (h : auxSeq A M n ≠ ⊤) :
    auxSeq A M n < auxSeq A M (n + 1) := by
  rw [auxSeq_succ_of_ne_top h]
  nth_rw 1 [← (auxSeq A M n).ker_mkQ]
  rw [LinearMap.ker, Submodule.comap_lt_comap_iff_of_surjective (auxSeq A M n).mkQ_surjective,
    bot_lt_iff_ne_bot]
  by_contra! H
  rw [LinearMap.range_eq_bot] at H
  have : Subsingleton (A ⧸ (auxP h).1) := subsingleton_iff.2 fun x y ↦
    auxLinearMap_injective h (by simp [H])
  exact false_of_nontrivial_of_subsingleton (A ⧸ (auxP h).1)

variable (A M) in
private theorem monotone_auxSeq : Monotone (auxSeq A M) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  by_cases h : auxSeq A M n = ⊤
  · simp [auxSeq_succ_of_eq_top h]
  exact (lt_auxSeq_succ_of_ne_top h).le

private theorem auxSeq_eq_auxSeq_succ_iff : auxSeq A M n = auxSeq A M (n + 1) ↔ auxSeq A M n = ⊤ :=
  ⟨not_imp_not.1 fun h ↦ (lt_auxSeq_succ_of_ne_top h).ne,
    fun h ↦ h.trans (auxSeq_succ_of_eq_top h).symm⟩

private theorem isQuotientEquivQuotientPrime_auxSeq_of_ne_top (h : auxSeq A M n ≠ ⊤) :
    (auxSeq A M n).IsQuotientEquivQuotientPrime (auxSeq A M (n + 1)) := by
  rw [auxSeq_succ_of_ne_top h]
  have hle : auxSeq A M n ≤ (LinearMap.range (auxLinearMap h)).comap (auxSeq A M n).mkQ := by
    nth_rw 1 [← (auxSeq A M n).ker_mkQ]
    exact LinearMap.ker_le_comap _
  refine ⟨hle, auxP h, ⟨?_ ≪≫ₗ (LinearEquiv.ofInjective _ (auxLinearMap_injective h)).symm⟩⟩
  refine (Submodule.quotEquivOfEq _ _ ?_) ≪≫ₗ
    ((LinearMap.range (auxLinearMap h)).comapRestrict (auxSeq A M n).mkQ
      |>.quotKerEquivOfSurjective ((LinearMap.range (auxLinearMap h))
        |>.comapRestrict_surjective_of_surjective _ (auxSeq A M n).mkQ_surjective))
  simp [Submodule.submoduleOf, Submodule.comapRestrict, LinearMap.ker_restrict, Submodule.ker_mkQ]

end

variable (A M)

/-- If `A` is a Noetherian ring and `M` is a finitely generated `A`-module, then there exists
a chain of submodules `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
`Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`. -/
@[stacks 00L0]
theorem IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime :
    ∃ s : RelSeries (Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M)),
      s.head = ⊥ ∧ s.last = ⊤ := by
  have H : ∃ n : ℕ, auxSeq A M n = ⊤ := by
    obtain ⟨n, h⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstanceAs (IsNoetherian A M))
      ⟨_, monotone_auxSeq A M⟩
    exact ⟨n, auxSeq_eq_auxSeq_succ_iff.1 (h (n + 1) n.lt_add_one.le)⟩
  classical exact ⟨⟨Nat.find H, fun ⟨n, _⟩ ↦ auxSeq A M n,
    fun ⟨n, h⟩ ↦ isQuotientEquivQuotientPrime_auxSeq_of_ne_top (Nat.find_min H h)⟩,
      auxSeq_zero A M, Nat.find_spec H⟩

/-- If a property on finitely generated modules over a Noetherian ring satisfies that:

- it holds for zero module (it's formalized as it holds for any module which is subsingleton),
- it holds for `A ⧸ p` for every prime ideal `p` of `A` (to avoid universe problem,
  it's formalized as it holds for any module isomorphic to `A ⧸ p`),
- it is stable by short exact sequences,

then the property holds for every finitely generated modules.

NOTE: This should be the induction principle for `M`, but due to the bug
https://github.com/leanprover/lean4/issues/4246
currently it is induction for `Module.Finite A M`. -/
@[elab_as_elim]
theorem IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    ⦃M : Type v⦄ [AddCommGroup M] [Module A M] (_ : Module.Finite A M)
    {motive : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] → Prop}
    (subsingleton : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] →
      [Subsingleton N] → motive N)
    (quotient : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] →
      (p : PrimeSpectrum A) → (N ≃ₗ[A] A ⧸ p.1) → motive N)
    (exact : (N₁ : Type v) → [AddCommGroup N₁] → [Module A N₁] → [Module.Finite A N₁] →
      (N₂ : Type v) → [AddCommGroup N₂] → [Module A N₂] → [Module.Finite A N₂] →
      (N₃ : Type v) → [AddCommGroup N₃] → [Module A N₃] → [Module.Finite A N₃] →
      (f : N₁ →ₗ[A] N₂) → (g : N₂ →ₗ[A] N₃) →
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      motive N₁ → motive N₃ → motive N₂) : motive M := by
  have equiv (N₁ : Type v) [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
      (N₂ : Type v) [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
      (f : N₁ ≃ₗ[A] N₂) (h : motive N₁) : motive N₂ :=
    exact N₁ N₂ PUnit.{v + 1} f 0 f.injective (Function.surjective_to_subsingleton _)
      ((f.exact_zero_iff_surjective _).2 f.surjective) h (subsingleton _)
  obtain ⟨s, hs1, hs2⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A M
  suffices H : ∀ n, (h : n < s.length + 1) → motive (s ⟨n, h⟩) by
    replace H : motive s.last := H s.length s.length.lt_add_one
    rw [hs2] at H
    exact equiv _ _ Submodule.topEquiv H
  intro n h
  induction n with
  | zero =>
    change motive s.head
    rw [hs1]
    exact subsingleton _
  | succ n ih =>
    specialize ih (n.lt_add_one.trans h)
    obtain ⟨hle, p, ⟨f⟩⟩ := s.step ⟨n, (add_lt_add_iff_right _).1 h⟩
    replace ih := equiv _ _ (Submodule.submoduleOfEquivOfLe hle).symm ih
    exact exact _ _ _ _ _ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _) ih (quotient _ p f)

/-- There are only finitely many associated primes of a finitely generated module
over a Noetherian ring. -/
@[stacks 00LC]
theorem associatedPrimes.finite : (associatedPrimes A M).Finite := by
  induction ‹Module.Finite A M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => simp [associatedPrimes.eq_empty_of_subsingleton]
  | quotient N p f =>
    have := associatedPrimes.eq_singleton_of_isPrimary p.2.isPrimary
    simp [LinearEquiv.AssociatedPrimes.eq f, this]
  | exact N₁ N₂ N₃ f g hf _ hfg h₁ h₃ =>
    exact (h₁.union h₃).subset (associatedPrimes.subset_union_of_exact f g hf hfg)
