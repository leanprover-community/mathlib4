/-
Copyright (c) 2025 Jinzhao Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Pan
-/
module

public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.Tactic.TermCongr
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Disjoint
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# Finitely generated module over Noetherian ring have finitely many associated primes.

In this file we proved that any finitely generated module over a Noetherian ring have finitely many
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

@[expose] public section

universe u v

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- A `Prop` asserting that two submodules `N₁, N₂` satisfy `N₁ ≤ N₂` and
`N₂ / N₁` is isomorphic to `A / p` for some prime ideal `p` of `A`. -/
def Submodule.IsQuotientEquivQuotientPrime (N₁ N₂ : Submodule A M) :=
  N₁ ≤ N₂ ∧ ∃ (p : PrimeSpectrum A), Nonempty ((↥N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[A] A ⧸ p.1)

set_option backward.isDefEq.respectTransparency false in
open LinearMap in
theorem Submodule.isQuotientEquivQuotientPrime_iff {N₁ N₂ : Submodule A M} :
    N₁.IsQuotientEquivQuotientPrime N₂ ↔
      ∃ x, Ideal.IsPrime ((⊥ : Submodule A (M ⧸ N₁)).colon {N₁.mkQ x}) ∧ N₂ = N₁ ⊔ span A {x} := by
  let f := mapQ (N₁.submoduleOf N₂) N₁ N₂.subtype le_rfl
  have hf₁ : ker f = ⊥ := ker_liftQ_eq_bot _ _ _ (by simp [ker_comp, submoduleOf])
  have hf₂ : range f = N₂.map N₁.mkQ := by simp [f, mapQ, range_liftQ, range_comp]
  refine ⟨fun ⟨h, p, ⟨e⟩⟩ ↦ ?_, fun ⟨x, hx, hx'⟩ ↦ ⟨le_sup_left.trans_eq hx'.symm, ⟨_, hx⟩, ?_⟩⟩
  · obtain ⟨⟨x, hx⟩, hx'⟩ := Submodule.mkQ_surjective _ (e.symm 1)
    have hx'' : N₁.mkQ x = f (e.symm 1) := by simp [f, ← hx']
    refine ⟨x, ?_, ?_⟩
    · convert p.2
      ext r
      simp [hx'', ← map_smul, Algebra.smul_def, show f _ = 0 ↔ _ from congr(_ ∈ $hf₁),
        Ideal.Quotient.eq_zero_iff_mem]
    · refine le_antisymm ?_ (sup_le h ((span_singleton_le_iff_mem _ _).mpr hx))
      have : (span A {x}).map N₁.mkQ = ((span A {1}).map e.symm.toLinearMap).map f := by
        simp only [map_span, Set.image_singleton, hx'', LinearEquiv.coe_coe]
      rw [← N₁.ker_mkQ, sup_comm, ← comap_map_eq, ← map_le_iff_le_comap, this]
      simp [hf₂, Ideal.Quotient.span_singleton_one]
  · have hxN₂ : x ∈ N₂ := (le_sup_right.trans_eq hx'.symm) (mem_span_singleton_self x)
    refine ⟨.symm (.ofBijective (Submodule.mapQ _ _ (toSpanSingleton A _ ⟨x, hxN₂⟩) ?_) ⟨?_, ?_⟩)⟩
    · simp [SetLike.le_def, ← Quotient.mk_smul, submoduleOf]
    · refine ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ ?_)
      simp [← Quotient.mk_smul, SetLike.le_def, submoduleOf]
    · rw [mapQ, ← range_eq_top, range_liftQ, range_comp]
      have := congr($(hx').submoduleOf N₂)
      rw [submoduleOf_self, submoduleOf_sup_of_le (by simp_all) (by simp_all),
        submoduleOf_span_singleton_of_mem _ hxN₂] at this
      simpa [← span_singleton_eq_range, LinearMap.range_toSpanSingleton] using this.symm

variable (A M) [IsNoetherianRing A] [Module.Finite A M]

/-- If `A` is a Noetherian ring and `M` is a finitely generated `A`-module, then there exists
a chain of submodules `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
`Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`. -/
@[stacks 00L0]
theorem IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime :
    ∃ s : RelSeries {(N₁, N₂) | Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M) N₁ N₂},
      s.head = ⊥ ∧ s.last = ⊤ := by
  refine WellFoundedGT.induction_top ⟨⊥, .singleton _ ⊥, rfl, rfl⟩ ?_
  rintro N hN ⟨s, hs₁, hs₂⟩
  have := Submodule.Quotient.nontrivial_iff.mpr hN
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A (M ⧸ N)
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, x, rfl⟩ := hp
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  have hxN : x ∉ N := fun h ↦ hp.ne_top (by rw [show N.mkQ x = 0 by simpa]; simp)
  have := Submodule.isQuotientEquivQuotientPrime_iff.mpr ⟨x, hp, rfl⟩
  refine ⟨_, by simpa [hs₂], s.snoc _ (hs₂ ▸ this), by simpa, rfl⟩

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
    exact (h₁.union h₃).subset (associatedPrimes.subset_union_of_exact hf hfg)

/-- Every maximal ideal of a commutative Noetherian total ring of fractions `A` is
an associated prime of the `A`-module `A`. -/
theorem Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing [IsFractionRing A A]
    (I : Ideal A) [hI : I.IsMaximal] : I ∈ associatedPrimes A A :=
  have fin := associatedPrimes.finite A A
  have ⟨P, hP⟩ := (I.subset_union_prime_finite fin (f := id) 0 0 fun _ h _ _ ↦ h.isPrime).1 <| by
    simp_rw [id, biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact fun x hx h ↦ hI.ne_top <| I.eq_top_of_isUnit_mem hx
      (IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_› h)
  hI.eq_of_le hP.1.isPrime.ne_top hP.2 ▸ hP.1

/-- A commutative Noetherian total ring of fractions is semilocal. -/
instance [IsFractionRing A A] : Finite (MaximalSpectrum A) :=
  (MaximalSpectrum.equivSubtype A).finite_iff.mpr <| Set.finite_coe_iff.mpr <|
    (associatedPrimes.finite A A).subset fun _ ↦ (·.mem_associatedPrimes_of_isFractionRing)

variable {A}

/-- An ideal consisting of zero divisors in a commutative Noetherian ring is annihilated by
some nonzero element. This is not true in general for finitely generated modules in commutative
rings, see https://math.stackexchange.com/q/1189814 and http://dx.doi.org/10.2140/pjm.1979.83.375
(keywords: Property (A), Quentel's Condition (C)).

It is also not true that every finitely generated module over every commutative Noetherian ring
is annihilated by some nonzero element if each element is annihilated by some nonzero element,
see https://math.stackexchange.com/a/3187153. -/
theorem Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors {I : Ideal A}
    (h : Disjoint (I : Set A) (nonZeroDivisors A)) : ⊥ < Module.annihilator A I := by
  obtain ⟨P, h, hP⟩ : ∃ P ∈ associatedPrimes A A, I ≤ P :=
    (I.subset_union_prime_finite (associatedPrimes.finite ..) (f := id) 0 0 fun _ h _ _ ↦ h.1).1 <|
    biUnion_associatedPrimes_eq_compl_nonZeroDivisors A ▸ h.subset_compl_right
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at h
  obtain ⟨prime, x, rfl⟩ := h
  exact SetLike.lt_iff_le_and_exists.mpr ⟨bot_le, x, Submodule.mem_annihilator.mpr <| by
    simpa only [smul_eq_mul, mul_comm x, SetLike.le_def, Submodule.mem_colon_singleton] using hP,
      fun h : x = 0 ↦ prime.ne_top <| by simp [h]⟩

theorem Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul {I : Ideal A} [FaithfulSMul A I] :
    ((I : Set A) ∩ nonZeroDivisors A).Nonempty := by
  by_contra!
  exact (bot_lt_annihilator_of_disjoint_nonZeroDivisors
    (Set.disjoint_iff_inter_eq_empty.mpr this)).ne' <| by rwa [Module.annihilator_eq_bot]
