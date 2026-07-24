/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Defs

/-! # Counting ideals of bounded norm in rings with finite quotients

For a ring with finite quotients, there are only finitely many ideals of bounded norm. This file
collects the resulting finiteness and `Northcott` results.

## Main results
- `Ring.HasFiniteQuotients.finite_cardQuot_le`: a ring with finite quotients has only finitely many
  ideals of norm bounded by `B`.
- `Ring.HasFiniteQuotients.finite_absNorm_le`: the analogous statement for `Ideal.absNorm`.

-/

public section

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R] [HasFiniteQuotients R]

theorem finite_setOfPred_mem (x : R) (hx : x ≠ 0) : {I : Ideal R | x ∈ I}.Finite := by
  have := finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hx)
  have : {I | Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) ⊥ ≤ I}.Finite :=
    .of_equiv _ (Ideal.relIsoOfSurjective _ Ideal.Quotient.mk_surjective).toEquiv
  simpa [← RingHom.ker_eq_comap_bot] using this

@[deprecated (since := "2026-07-09")] alias finite_setOf_mem := finite_setOfPred_mem

open scoped Pointwise in
/-- For every bound `B`, a ring with finite quotients has only finitely many ideals of norm bounded
by `B`. -/
theorem finite_cardQuot_le (B : ℕ) : {I : Ideal R | I.cardQuot ≤ B}.Finite := by
  classical
  rcases finite_or_infinite R
  · apply Set.toFinite
  -- if `R` is infinite, then we can pick a finite set `s` of cardinality `B + 1`
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq R (B + 1)
  -- and consider the finite set `t` of nonzero differences
  let t := (s - s) \ {0}
  refine Set.Finite.of_sdiff ?_ (Set.finite_singleton ⊥)
  -- in a ring with finite quotients, each nonzero element is contained in only finitely many ideals
  -- so it is enough to show that each ideal `I` of norm at most `B` contains some element of `t`
  suffices {I | Submodule.cardQuot I ≤ B} \ {⊥} ⊆ ⋃ x ∈ t, {I | x ∈ I} from
    (t.finite_toSet.biUnion fun x hx ↦ finite_setOfPred_mem x (by grind)).subset this
  intro I hI
  rw [Set.mem_sdiff, Set.mem_ofPred, Submodule.cardQuot_apply] at hI
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
  -- `s` has cardinality `B + 1`, but the quotient `R ⧸ I` has cardinality at most `B`
  replace hs : (s.image (Ideal.Quotient.mk I)).card < s.card := by
    have := finiteQuotient hI.2
    have := Fintype.ofFinite (R ⧸ I)
    grw [Finset.card_le_univ, Fintype.card_eq_nat_card, hI.1, hs, Nat.lt_add_one_iff]
  -- so we can find distinct `x, y ∈ s` with the desired collision `x - y ∈ I`
  obtain ⟨x, hx, y, hy, hxy, h⟩ := Finset.exists_ne_map_eq_of_card_image_lt hs
  refine ⟨x - y, ?_, (Submodule.Quotient.eq I).mp h⟩
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
  rwa [Finset.notMem_singleton, sub_ne_zero]

/-- A ring with finite quotients has only finitely many ideals of bounded norm. -/
theorem finite_absNorm_le [IsDedekindDomain R] [Infinite R] (B : ℕ) :
    {I : Ideal R | I.absNorm ≤ B}.Finite :=
  finite_cardQuot_le B

/-- A ring with finite quotients has only finitely many nonzero prime ideals of bounded norm. -/
theorem finite_cardQuot_heightOneSpectrum_le (B : ℕ) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.cardQuot ≤ B}.Finite :=
  (finite_cardQuot_le B).of_injOn (by simp [Set.MapsTo])
    (Function.Injective.injOn fun _ _ ↦ IsDedekindDomain.HeightOneSpectrum.ext)

/-- A ring with finite quotients has only finitely many nonzero prime ideals of bounded norm. -/
theorem finite_absNorm_heightOneSpectrum_le [IsDedekindDomain R] [Infinite R] (B : ℕ) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.absNorm ≤ B}.Finite :=
  finite_cardQuot_heightOneSpectrum_le B

instance : Northcott fun p : Ideal R ↦ p.cardQuot :=
  ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩

instance [IsDedekindDomain R] [Infinite R] :
    Northcott fun p : IsDedekindDomain.HeightOneSpectrum R ↦ p.asIdeal.absNorm :=
  ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

end Ring.HasFiniteQuotients
