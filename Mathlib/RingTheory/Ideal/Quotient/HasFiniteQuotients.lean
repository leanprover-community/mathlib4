/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Height.Northcott
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Rings with finite quotients

A commutative ring is said to have finite quotients if, for any nonzero ideal `I` of `R`, the
quotient `R ⧸ I` is finite.

## Main results
- `Ring.HasFiniteQuotients.instDimensionLEOne`: A ring with finite quotients has dimension `≤ 1`.
- `Ring.HasFiniteQuotients.instIsNoetherianRing` : A ring with finite quotients is noetherian.
- `Ring.HasFiniteQuotients.of_module_finite`: Assume that `R` has finite quotients and that `S` is
  a domain and a finite `R`-module. Then `S` has finite quotients.
- `Ring.HasFiniteQuotients.instOfIsDomainOfFG`: A domain that is also a finite `ℤ`-module
  has finite quotients.

-/

@[expose] public section

/--
A ring `R` has finite quotients if the quotient `R ⧸ I` is finite for all nonzero ideals of `R`.
-/
class Ring.HasFiniteQuotients (R : Type*) [CommRing R] : Prop where
  finiteQuotient {I : Ideal R} : I ≠ ⊥ → Finite (R ⧸ I)

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R]

/-- A finite ring has finite quotients. -/
instance [Finite R] : Ring.HasFiniteQuotients R where
  finiteQuotient := fun _ ↦ Quotient.finite _

section properties

variable [HasFiniteQuotients R]

/-- A nonzero prime ideal of a ring with finite quotients is maximal. -/
theorem maximalOfPrime {P : Ideal R} [P.IsPrime] (hp : P ≠ ⊥) :
    P.IsMaximal :=
  have : Finite (R ⧸ P) := finiteQuotient hp
  Ideal.Quotient.maximal_of_isField P <| Finite.isField_of_domain (R ⧸ P)

/-- A ring with finite quotients has dimension `≤ 1`. -/
instance : DimensionLEOne R where
  maximalOfPrime := fun h _ ↦ maximalOfPrime h

/-- A ring with finite quotients is noetherian. -/
instance : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I ↦ ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I := Ideal.span {x}) (by simp [hx₂])
    exact Submodule.FG.of_finite
  · rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hx₁)]
    exact Submodule.fg_span_singleton x

theorem cardQuot_pos (I : Ideal R) (hI : I ≠ ⊥) : 0 < I.cardQuot := by
  have := finiteQuotient hI
  rw [Submodule.cardQuot_apply]
  exact Nat.card_pos

theorem finite_setOf_mem (x : R) (hx : x ≠ 0) : {I : Ideal R | x ∈ I}.Finite := by
  have := finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hx)
  have : {I | Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) ⊥ ≤ I}.Finite :=
    .of_equiv _ (Ideal.relIsoOfSurjective _ Ideal.Quotient.mk_surjective).toEquiv
  simpa [← RingHom.ker_eq_comap_bot] using this

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
  refine Set.Finite.of_diff ?_ (Set.finite_singleton ⊥)
  -- in a ring with finite quotients, each nonzero element is contained in only finitely many ideals
  -- so it is enough to show that each ideal `I` of norm at most `B` contains some element of `t`
  suffices {I | Submodule.cardQuot I ≤ B} \ {⊥} ⊆ ⋃ x ∈ t, {I | x ∈ I} from
    (t.finite_toSet.biUnion fun x hx ↦ finite_setOf_mem x (by grind)).subset this
  intro I hI
  rw [Set.mem_diff, Set.mem_setOf, Submodule.cardQuot_apply] at hI
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
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
theorem finite_absNorm_le [IsDedekindDomain R] [Module.Free ℤ R] (B : ℕ) :
    {I : Ideal R | I.absNorm ≤ B}.Finite :=
  finite_cardQuot_le B

/-- A ring with finite quotients has only finitely many nonzero prime ideals of bounded norm. -/
theorem finite_cardQuot_heightOneSpectrum_le (B : ℕ) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.cardQuot ≤ B}.Finite :=
  (finite_cardQuot_le B).of_injOn (by simp [Set.MapsTo])
    (Function.Injective.injOn fun _ _ ↦ IsDedekindDomain.HeightOneSpectrum.ext)

/-- A ring with finite quotients has only finitely many nonzero prime ideals of bounded norm. -/
theorem finite_absNorm_heightOneSpectrum_le [IsDedekindDomain R] [Module.Free ℤ R] (B : ℕ) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.absNorm ≤ B}.Finite :=
  finite_cardQuot_heightOneSpectrum_le B

instance : Northcott fun p : Ideal R ↦ p.cardQuot :=
  ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩

instance [IsDedekindDomain R] [Module.Free ℤ R] :
    Northcott fun p : IsDedekindDomain.HeightOneSpectrum R ↦ p.asIdeal.absNorm :=
  ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

variable (R) in
/--
Assume that `R` has finite quotients and that `S` is a domain and a finite `R`-module. Then
`S` has finite quotients.
-/
theorem of_module_finite (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] :
    HasFiniteQuotients S where
  finiteQuotient {I} hI := by
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Finite S := Module.finite_of_finite R
      exact Quotient.finite _
    let J : Ideal R := Ideal.under R I
    have : Finite (R ⧸ J) := finiteQuotient <| Ideal.under_ne_bot R hI
    have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact Module.finite_of_finite (R ⧸ J)

end properties

/-- The ring `ℤ` has finite quotients. -/
instance : HasFiniteQuotients ℤ where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
    have : NeZero n := ⟨by simpa using hI⟩
    exact inferInstanceAs <| Finite (ℤ ⧸ Ideal.span {n})

/-- A domain that is finitely generated has finite quotients. -/
instance [IsDomain R] [AddGroup.FG R] : HasFiniteQuotients R :=
  of_module_finite ℤ R

end Ring.HasFiniteQuotients
