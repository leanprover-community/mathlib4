/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKTwoCharge
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The unique-balanced-channel DvdK, and the cancellation dichotomy

This is the general (any-support, complex-coefficient) form of the two-charge argument in
`DvdKTwoCharge`.  There the balanced composition of size `p+n` is unique *because* the
support has two charges; here we take uniqueness as a hypothesis and get the same conclusion for
**arbitrary support** and **arbitrary number of charges**:

> if some size `m` has a UNIQUE balanced composition `r0`, then `CT(f^m)` is a single
> uncancellable multinomial term, so it is nonzero for every choice of nonzero coefficients.

No positivity is needed — the single surviving term cannot be cancelled by anything because there
is nothing else in the sum.  This removes the `DvdK1` premise on every support that has a unique
minimal balanced channel (the bulk of supports; the residual "coincident-channel" stratum, where a
size carries ≥2 balanced compositions, is exactly where cancellation can occur and where the Galois
orbit-product argument is required).

The contrapositive `two_balanced_of_ct_zero` states that dichotomy inside Lean: **cancellation at
size `m` forces at least two distinct balanced compositions of size `m`.**
-/

open MvPolynomial Finset

namespace GMC2.DvdKUniqueChannel

/-- **Unique-balanced-channel DvdK (any support, complex coefficients).**  If `r0` is the *only*
balanced composition of size `m`, then `CT(f^m) ≠ 0` for any nonzero coefficient vector `c`.  The
constant term collapses to the single term `multinomial(r0)·∏ c_i^{r0 i}`, which cannot vanish. -/
theorem ct_ne_zero_of_unique_balanced {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (m : ℕ)
    (r0 : ι → ℕ)
    (hr0 : r0 ∈ Finset.piAntidiag (Finset.univ : Finset ι) m)
    (hbal : GMC2.ConstantTermRelations.totalCharge q r0 = 0)
    (huniq : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
      GMC2.ConstantTermRelations.totalCharge q r = 0 → r = r0) :
    MvPolynomial.aeval c
      (GMC2.ConstantTermRelations.constantTermRelation q m) ≠ 0 := by
  rw [GMC2.ConstantTermRelations.aeval_constantTermRelation]
  rw [Finset.sum_eq_single r0]
  · rw [if_pos hbal]
    have hmult : (Nat.multinomial Finset.univ r0 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.multinomial_pos Finset.univ r0).ne'
    exact mul_ne_zero hmult
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hc i)))
  · intro r hr hne
    exact if_neg (fun hbalr => hne (huniq r hr hbalr))
  · intro h; exact absurd hr0 h

/-- **The cancellation dichotomy (contrapositive).** If `CT(f^m) = 0` at nonzero coefficients while
`r0` is a balanced composition of size `m`, then there is a *second*, distinct balanced composition
of the same size. So cancellation is impossible without ≥2 coincident balanced channels — this is
the precise place where the elementary argument stops and the orbit-product argument (Galois
orbit-product) is needed. -/
theorem two_balanced_of_ct_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (m : ℕ)
    (r0 : ι → ℕ)
    (hr0 : r0 ∈ Finset.piAntidiag (Finset.univ : Finset ι) m)
    (hbal : GMC2.ConstantTermRelations.totalCharge q r0 = 0)
    (hzero : MvPolynomial.aeval c
      (GMC2.ConstantTermRelations.constantTermRelation q m) = 0) :
    ∃ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
      GMC2.ConstantTermRelations.totalCharge q r = 0 ∧ r ≠ r0 := by
  by_contra h
  refine ct_ne_zero_of_unique_balanced q c hc m r0 hr0 hbal ?_ hzero
  intro r hr hbalr
  by_contra hne
  exact h ⟨r, hr, hbalr, hne⟩

/-- The set of balanced compositions of size `m` — the "channels" of mass `m`.  Its cardinality is
the coincident-cycle count that stratifies supports (`card = 1` for the
DvdK-free 84%, `card ≥ 2` for the hard resonant stratum). -/
def balancedSet {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℤ) (m : ℕ) : Finset (ι → ℕ) :=
  (Finset.piAntidiag (Finset.univ : Finset ι) m).filter
    (fun r => GMC2.ConstantTermRelations.totalCharge q r = 0)

/-- **Unique channel (card = 1) ⟹ no cancellation.**  The `Finset`-cardinality form of
`ct_ne_zero_of_unique_balanced`: a single balanced channel of mass `m` forces `CT(f^m) ≠ 0`.  This
is the unique-primitive-cycle criterion, mechanized. -/
theorem ct_ne_zero_of_card_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (m : ℕ)
    (hcard : (balancedSet q m).card = 1) :
    MvPolynomial.aeval c
      (GMC2.ConstantTermRelations.constantTermRelation q m) ≠ 0 := by
  obtain ⟨r0, hr0eq⟩ := Finset.card_eq_one.mp hcard
  have hr0mem : r0 ∈ balancedSet q m := hr0eq ▸ Finset.mem_singleton_self r0
  rw [balancedSet, Finset.mem_filter] at hr0mem
  obtain ⟨hr0pi, hr0bal⟩ := hr0mem
  refine ct_ne_zero_of_unique_balanced q c hc m r0 hr0pi hr0bal ?_
  intro r hrpi hrbal
  have hrmem : r ∈ balancedSet q m := Finset.mem_filter.mpr ⟨hrpi, hrbal⟩
  rw [hr0eq, Finset.mem_singleton] at hrmem
  exact hrmem

/-- **Cancellation ⟹ ≥2 coincident channels (card ≥ 2).** The `Finset`-cardinality form of the
dichotomy: if `CT(f^m) = 0` while at least one balanced channel exists, there are at least two. So
cancellation lives exactly on the coincident-cycle stratum (the hard coincident-cycle stratum),
where the orbit-product argument's Galois orbit-product is required. -/
theorem two_le_card_balanced_of_ct_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (m : ℕ)
    (hne : (balancedSet q m).Nonempty)
    (hzero : MvPolynomial.aeval c
      (GMC2.ConstantTermRelations.constantTermRelation q m) = 0) :
    2 ≤ (balancedSet q m).card := by
  obtain ⟨r0, hr0⟩ := hne
  rw [balancedSet, Finset.mem_filter] at hr0
  obtain ⟨hr0pi, hr0bal⟩ := hr0
  obtain ⟨r, hrpi, hrbal, hrne⟩ := two_balanced_of_ct_zero q c hc m r0 hr0pi hr0bal hzero
  have hr0mem : r0 ∈ balancedSet q m := Finset.mem_filter.mpr ⟨hr0pi, hr0bal⟩
  have hrmem : r ∈ balancedSet q m := Finset.mem_filter.mpr ⟨hrpi, hrbal⟩
  exact Finset.one_lt_card.mpr ⟨r, hrmem, r0, hr0mem, hrne⟩

/-- **DvdK1 is a *theorem* on unique-channel supports** — no DvdK premise.  If some size `m0 ≥ 1`
carries a unique balanced composition, the exact DvdK1 existential conclusion
(`∃ m ≥ 1, CT(f^m) ≠ 0`) holds outright.  This is the shape consumed by the GMC(2) spine
(`GMC2.DvdKInterface.DvdK1` / `exists_nonzero_face_seed`), so it discharges that input for the whole
unique-channel class (the generic stratum of supports) without any external analytic axiom. -/
theorem dvdk1_of_uniqueChannel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (hUC : ∃ m0 : ℕ, 1 ≤ m0 ∧ ∃ r0 : ι → ℕ,
      r0 ∈ Finset.piAntidiag (Finset.univ : Finset ι) m0 ∧
      GMC2.ConstantTermRelations.totalCharge q r0 = 0 ∧
      ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m0,
        GMC2.ConstantTermRelations.totalCharge q r = 0 → r = r0) :
    ∃ m : ℕ, 1 ≤ m ∧
      MvPolynomial.aeval c
        (GMC2.ConstantTermRelations.constantTermRelation q m) ≠ 0 := by
  obtain ⟨m0, hm0, r0, hr0mem, hr0bal, huniq⟩ := hUC
  exact ⟨m0, hm0, ct_ne_zero_of_unique_balanced q c hc m0 r0 hr0mem hr0bal huniq⟩

/-- The two-charge theorem of `DvdKTwoCharge` is the `Fin 2` instance of the general
unique-channel lemma: `balanced_unique` supplies the uniqueness hypothesis. -/
theorem two_charge_via_unique (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (c : Fin 2 → ℂ) (hc : ∀ i, c i ≠ 0) :
    MvPolynomial.aeval c
      (GMC2.ConstantTermRelations.constantTermRelation
        (GMC2.DvdKTwoCharge.pairQ p n) (p + n)) ≠ 0 :=
  ct_ne_zero_of_unique_balanced (GMC2.DvdKTwoCharge.pairQ p n) c hc (p + n)
    (GMC2.DvdKTwoCharge.pairR p n) (GMC2.DvdKTwoCharge.pairR_mem p n)
    (GMC2.DvdKTwoCharge.pairR_balanced p n)
    (fun r hr hbal => GMC2.DvdKTwoCharge.balanced_unique p n hp hn r hr hbal)

end GMC2.DvdKUniqueChannel

