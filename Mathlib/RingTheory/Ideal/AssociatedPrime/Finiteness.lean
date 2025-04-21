/-
Copyright (c) 2025 Jinzhao Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Pan
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!

# Finitely generated module over noetherian ring have finitely many associated primes.

In this file we proved that any finitely generated module over a noetherian ring have finitely many
associated primes.

# Main definitions and results

* `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` : If `A` is a Noetherian ring
and `M` is a finitely generated `A`-module, then there exists a chain of submodules
`0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
`Mᵢ₊1 / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`.

* `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` : If a property on
finitely generated modules over a Noetherian ring satisfies that:
- it holds for zero module,
- it holds for any module isomorphic to some `A ⧸ p` where `p` is a prime ideal of `A`,
- it is stable by short exact sequences,
then the property holds for every finitely generated modules.

* `associatedPrimes.subset_union_of_exact` : If `0 → M → M' → M''` is an exact sequence,
then the set of associated primes of `M'` is contained in the union of those of `M` and `M''`.

* `associatedPrimes.finite` : There are only finitely many associated primes of a
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
  have H := associatedPrimes.nonempty A (M ⧸ N)
  have hprime := (AssociatePrimes.mem_iff.1 H.some_mem).1
  obtain ⟨a, ha⟩ := (AssociatePrimes.mem_iff.1 H.some_mem).2
  exact ⟨⟨_, hprime⟩, Submodule.liftQ _ _ ha.le,
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot' _ _ ha)⟩

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

namespace Submodule

variable {R M M₁ : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁]
  [Module R M] [Module R M₁] (q : Submodule R M₁) (f : M →ₗ[R] M₁)

/-- For a linear map `f`, the map from `q.comap f` to `q` for a submodule `q`
obtained from restricting `f` -/
def comapRestrict : ↥(q.comap f) →ₗ[R] ↥q :=
  f.restrict fun _ hx ↦ mem_comap.mp hx

@[simp]
theorem comapRestrict_coe_apply (x : q.comap f) : (q.comapRestrict f) x = f x := rfl

theorem comapRestrict_surjective_of_surjective (hf : Function.Surjective f) :
    Function.Surjective (q.comapRestrict f) := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

end Submodule

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
`Mᵢ₊1 / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`. -/
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

/-- If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of `M'` is
contained in the union of those of `M` and `M''`. -/
@[stacks 02M3 "second part"]
theorem associatedPrimes.subset_union_of_exact
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] {M'' : Type*} [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'') (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∪ associatedPrimes R M'' := by
  rintro p ⟨_, x, hx⟩
  by_cases h : ∃ a ∈ p.primeCompl, ∃ y : M, f y = a • x
  · obtain ⟨a, ha, y, h⟩ := h
    refine Or.inl ⟨‹_›, y, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
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
    refine Or.inr ⟨‹_›, g x, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb ⊢
      rw [← map_smul, hb, map_zero]
    · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra! H
      exact h b H y hy

/-- The set of associated primes of the product of two modules is equal to
the union of those of the two modules. -/
@[stacks 02M3 "third part"]
theorem associatedPrimes.prod
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (M' : Type*) [AddCommGroup M'] [Module R M'] :
    associatedPrimes R (M × M') = associatedPrimes R M ∪ associatedPrimes R M' :=
  (subset_union_of_exact (.inl R M M') (.snd R M M') LinearMap.inl_injective .inl_snd).antisymm
    (Set.union_subset_iff.2 ⟨subset_of_injective (.inl R M M') LinearMap.inl_injective,
      subset_of_injective (.inr R M M') LinearMap.inr_injective⟩)

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
