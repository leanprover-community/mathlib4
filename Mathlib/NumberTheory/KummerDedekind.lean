/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IsAdjoinRoot

#align_import number_theory.kummer_dedekind from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Kummer-Dedekind theorem

This file proves the monogenic version of the Kummer-Dedekind theorem on the splitting of prime
ideals in an extension of the ring of integers. This states that if `I` is a prime ideal of
Dedekind domain `R` and `S = R[α]` for some `α` that is integral over `R` with minimal polynomial
`f`, then the prime factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the
same number of prime factors, and each prime factors of `I * S` can be paired with a prime factor
of `f mod I` in a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

 * `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` : The bijection in the
    Kummer-Dedekind theorem. This is the pairing between the prime factors of `I * S` and the prime
    factors of `f mod I`.

## Main results

 * `normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map` : The Kummer-Dedekind
    theorem.
 * `Ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebraMap R S)` is irreducible if
    `(map (Ideal.Quotient.mk I) (minpoly R pb.gen))` is irreducible, where `pb` is a power basis
    of `S` over `R`.

## TODO

 * Prove the Kummer-Dedekind theorem in full generality.

 * Prove the converse of `Ideal.irreducible_map_of_irreducible_minpoly`.

 * Prove that `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` can be expressed as
    `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk g = ⟨I, G(α)⟩` for `g` a prime
    factor of `f mod I` and `G` a lift of `g` to `R[X]`.

## References

 * [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/


variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid Algebra RingHom

local notation:max R "<" x:max ">" => adjoin R ({x} : Set S)

/-- Let `S / R` be a ring extension and `x : S`, then the conductor of `R<x>` is the
    biggest ideal of `S` contained in `R<x>`. -/
def conductor (x : S) : Ideal S where
  carrier := {a | ∀ b : S, a * b ∈ R<x>}
  zero_mem' b := by simpa only [zero_mul] using Subalgebra.zero_mem _
                    -- 🎉 no goals
                         -- 🎉 no goals
  add_mem' ha hb c := by simpa only [add_mul] using Subalgebra.add_mem _ (ha c) (hb c)
  smul_mem' c a ha b := by simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b)
                           -- 🎉 no goals
#align conductor conductor

variable {R} {x : S}

theorem conductor_eq_of_eq {y : S} (h : (R<x> : Set S) = R<y>) : conductor R x = conductor R y :=
  Ideal.ext fun _ => forall_congr' fun _ => Set.ext_iff.mp h _
#align conductor_eq_of_eq conductor_eq_of_eq

theorem conductor_subset_adjoin : (conductor R x : Set S) ⊆ R<x> := fun y hy => by
  simpa only [mul_one] using hy 1
  -- 🎉 no goals
#align conductor_subset_adjoin conductor_subset_adjoin

theorem mem_conductor_iff {y : S} : y ∈ conductor R x ↔ ∀ b : S, y * b ∈ R<x> :=
  ⟨fun h => h, fun h => h⟩
#align mem_conductor_iff mem_conductor_iff

theorem conductor_eq_top_of_adjoin_eq_top (h : R<x> = ⊤) : conductor R x = ⊤ := by
  simp only [Ideal.eq_top_iff_one, mem_conductor_iff, h, mem_top, forall_const]
  -- 🎉 no goals
#align conductor_eq_top_of_adjoin_eq_top conductor_eq_top_of_adjoin_eq_top

theorem conductor_eq_top_of_powerBasis (pb : PowerBasis R S) : conductor R pb.gen = ⊤ :=
  conductor_eq_top_of_adjoin_eq_top pb.adjoin_gen_eq_top
#align conductor_eq_top_of_power_basis conductor_eq_top_of_powerBasis

variable {I : Ideal R}

/-- This technical lemma tell us that if `C` is the conductor of `R<x>` and `I` is an ideal of `R`
  then `p * (I * S) ⊆ I * R<x>` for any `p` in `C ∩ R` -/
theorem prod_mem_ideal_map_of_mem_conductor {p : R} {z : S}
    (hp : p ∈ Ideal.comap (algebraMap R S) (conductor R x)) (hz' : z ∈ I.map (algebraMap R S)) :
    algebraMap R S p * z ∈ algebraMap R<x> S '' ↑(I.map (algebraMap R R<x>)) := by
  rw [Ideal.map, Ideal.span, Finsupp.mem_span_image_iff_total] at hz'
  -- ⊢ ↑(algebraMap R S) p * z ∈ ↑(algebraMap { x_1 // x_1 ∈ adjoin R {x} } S) '' ↑ …
  obtain ⟨l, H, H'⟩ := hz'
  -- ⊢ ↑(algebraMap R S) p * z ∈ ↑(algebraMap { x_1 // x_1 ∈ adjoin R {x} } S) '' ↑ …
  rw [Finsupp.total_apply] at H'
  -- ⊢ ↑(algebraMap R S) p * z ∈ ↑(algebraMap { x_1 // x_1 ∈ adjoin R {x} } S) '' ↑ …
  rw [← H', mul_comm, Finsupp.sum_mul]
  -- ⊢ (Finsupp.sum l fun a c => c • ↑(algebraMap R S) a * ↑(algebraMap R S) p) ∈ ↑ …
  have lem : ∀ {a : R}, a ∈ I → l a • algebraMap R S a * algebraMap R S p ∈
      algebraMap R<x> S '' I.map (algebraMap R R<x>) := by
    intro a ha
    rw [Algebra.id.smul_eq_mul, mul_assoc, mul_comm, mul_assoc, Set.mem_image]
    refine Exists.intro
        (algebraMap R R<x> a * ⟨l a * algebraMap R S p,
          show l a * algebraMap R S p ∈ R<x> from ?_⟩) ?_
    · refine ⟨?_, ?_⟩
      · rw [mul_comm]
        exact mem_conductor_iff.mp (Ideal.mem_comap.mp hp) _
      · rw [mul_comm]
        apply Ideal.mul_mem_left (I.map (algebraMap R R<x>)) _ (Ideal.mem_map_of_mem _ ha)
      · simp only [RingHom.map_mul, mul_comm (algebraMap R S p) (l a)]
        rfl
  refine Finset.sum_induction _ (fun u => u ∈ algebraMap R<x> S '' I.map (algebraMap R R<x>))
      (fun a b => ?_) ?_ ?_
  rintro ⟨z, hz, rfl⟩ ⟨y, hy, rfl⟩
  rw [← RingHom.map_add]
  exact ⟨z + y, Ideal.add_mem _ (SetLike.mem_coe.mp hz) hy, rfl⟩
  -- ⊢ (fun u => u ∈ ↑(algebraMap { x_1 // x_1 ∈ adjoin R {x} } S) '' ↑(Ideal.map ( …
  · exact ⟨0, SetLike.mem_coe.mpr <| Ideal.zero_mem _, RingHom.map_zero _⟩
    -- 🎉 no goals
  · intro y hy
    -- ⊢ (fun a c => c • ↑(algebraMap R S) a * ↑(algebraMap R S) p) y (↑l y) ∈ ↑(alge …
    exact lem ((Finsupp.mem_supported _ l).mp H hy)
    -- 🎉 no goals
#align prod_mem_ideal_map_of_mem_conductor prod_mem_ideal_map_of_mem_conductor

/-- A technical result telling us that `(I * S) ∩ R<x> = I * R<x>` for any ideal `I` of `R`. -/
theorem comap_map_eq_map_adjoin_of_coprime_conductor
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (h_alg : Function.Injective (algebraMap R<x> S)) :
    (I.map (algebraMap R S)).comap (algebraMap R<x> S) = I.map (algebraMap R R<x>) := by
  apply le_antisymm
  -- ⊢ comap (algebraMap { x_1 // x_1 ∈ adjoin R {x} } S) (Ideal.map (algebraMap R  …
  · -- This is adapted from [Neukirch1992]. Let `C = (conductor R x)`. The idea of the proof
    -- is that since `I` and `C ∩ R` are coprime, we have
    -- `(I * S) ∩ R<x> ⊆ (I + C) * ((I * S) ∩ R<x>) ⊆ I * R<x> + I * C * S ⊆ I * R<x>`.
    intro y hy
    -- ⊢ y ∈ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin R {x} }) I
    obtain ⟨z, hz⟩ := y
    -- ⊢ { val := z, property := hz } ∈ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin …
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hx)
    -- ⊢ { val := z, property := hz } ∈ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin …
    have temp : algebraMap R S p * z + algebraMap R S q * z = z := by
      simp only [← add_mul, ← RingHom.map_add (algebraMap R S), hpq, map_one, one_mul]
    suffices z ∈ algebraMap R<x> S '' I.map (algebraMap R R<x>) ↔
        (⟨z, hz⟩ : R<x>) ∈ I.map (algebraMap R R<x>) by
      rw [← this, ← temp]
      obtain ⟨a, ha⟩ := (Set.mem_image _ _ _).mp (prod_mem_ideal_map_of_mem_conductor hp
          (show z ∈ I.map (algebraMap R S) by rwa [Ideal.mem_comap] at hy ))
      use a + algebraMap R R<x> q * ⟨z, hz⟩
      refine ⟨Ideal.add_mem (I.map (algebraMap R R<x>)) ha.left ?_, by
          simp only [ha.right, map_add, AlgHom.map_mul, add_right_inj]; rfl⟩
      rw [mul_comm]
      exact Ideal.mul_mem_left (I.map (algebraMap R R<x>)) _ (Ideal.mem_map_of_mem _ hq)
    refine ⟨fun h => ?_,
      fun h => (Set.mem_image _ _ _).mpr (Exists.intro ⟨z, hz⟩ ⟨by simp [h], rfl⟩)⟩
    · obtain ⟨x₁, hx₁, hx₂⟩ := (Set.mem_image _ _ _).mp h
      -- ⊢ { val := z, property := hz } ∈ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin …
      have : x₁ = ⟨z, hz⟩ := by
        apply h_alg
        simp [hx₂]
        rfl
      rwa [← this]
      -- 🎉 no goals
  · -- The converse inclusion is trivial
    have : algebraMap R S = (algebraMap _ S).comp (algebraMap R R<x>) := by ext; rfl
    -- ⊢ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin R {x} }) I ≤ comap (algebraMap …
    rw [this, ← Ideal.map_map]
    -- ⊢ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin R {x} }) I ≤ comap (algebraMap …
    apply Ideal.le_comap_map
    -- 🎉 no goals
#align comap_map_eq_map_adjoin_of_coprime_conductor comap_map_eq_map_adjoin_of_coprime_conductor

/-- The canonical morphism of rings from `R<x> ⧸ (I*R<x>)` to `S ⧸ (I*S)` is an isomorphism
    when `I` and `(conductor R x) ∩ R` are coprime. -/
noncomputable def quotAdjoinEquivQuotMap (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (h_alg : Function.Injective (algebraMap R<x> S)) :
    R<x> ⧸ I.map (algebraMap R R<x>) ≃+* S ⧸ I.map (algebraMap R S) := by
  let f : R<x> ⧸ I.map (algebraMap R R<x>) →+* S ⧸ I.map (algebraMap R S) :=
    (Ideal.Quotient.lift (I.map (algebraMap R R<x>))
      ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R<x> S)) (fun r hr => by
      have : algebraMap R S = (algebraMap R<x> S).comp (algebraMap R R<x>) := by ext; rfl
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, this, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hr))
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  -- ⊢ Function.Injective ↑f
  · --the kernel of the map is clearly `(I * S) ∩ R<x>`. To get injectivity, we need to show that
    --this is contained in `I * R<x>`, which is the content of the previous lemma.
    refine RingHom.lift_injective_of_ker_le_ideal _ _ fun u hu => ?_
    -- ⊢ u ∈ Ideal.map (algebraMap R { x_1 // x_1 ∈ adjoin R {x} }) I
    rwa [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      comap_map_eq_map_adjoin_of_coprime_conductor hx h_alg] at hu
  · -- Surjectivity follows from the surjectivity of the canonical map `R<x> → S ⧸ (I * S)`,
    -- which in turn follows from the fact that `I * S + (conductor R x) = S`.
    refine Ideal.Quotient.lift_surjective_of_surjective _ _ fun y => ?_
    -- ⊢ ∃ a, ↑(RingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (alge …
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective y
    -- ⊢ ∃ a, ↑(RingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (alge …
    have : z ∈ conductor R x ⊔ I.map (algebraMap R S) := by
      suffices conductor R x ⊔ I.map (algebraMap R S) = ⊤ by simp only [this, Submodule.mem_top]
      rw [Ideal.eq_top_iff_one] at hx ⊢
      replace hx := Ideal.mem_map_of_mem (algebraMap R S) hx
      rw [Ideal.map_sup, RingHom.map_one] at hx
      exact (sup_le_sup
        (show ((conductor R x).comap (algebraMap R S)).map (algebraMap R S) ≤ conductor R x
          from Ideal.map_comap_le)
          (le_refl (I.map (algebraMap R S)))) hx
    rw [← Ideal.mem_quotient_iff_mem_sup, hz, Ideal.mem_map_iff_of_surjective] at this
    -- ⊢ ∃ a, ↑(RingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (alge …
    obtain ⟨u, hu, hu'⟩ := this
    -- ⊢ ∃ a, ↑(RingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (alge …
    use ⟨u, conductor_subset_adjoin hu⟩
    -- ⊢ ↑(RingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (algebraMa …
    simp only [← hu']
    -- ⊢ ↑(RingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (algebraMa …
    rfl
    -- ⊢ Function.Surjective ↑(Ideal.Quotient.mk (Ideal.map (algebraMap R S) I))
    · exact Ideal.Quotient.mk_surjective
      -- 🎉 no goals
#align quot_adjoin_equiv_quot_map quotAdjoinEquivQuotMap

-- Porting note: on-line linter fails with `failed to synthesize` instance
-- but #lint does not report any problem
@[simp, nolint simpNF]
theorem quotAdjoinEquivQuotMap_apply_mk (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (h_alg : Function.Injective (algebraMap R<x> S)) (a : R<x>) :
    quotAdjoinEquivQuotMap hx h_alg (Ideal.Quotient.mk (I.map (algebraMap R R<x>)) a) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) ↑a := rfl
#align quot_adjoin_equiv_quot_map_apply_mk quotAdjoinEquivQuotMap_apply_mk

namespace KummerDedekind

open scoped BigOperators Polynomial Classical

variable [IsDomain R] [IsIntegrallyClosed R]

variable [IsDomain S] [IsDedekindDomain S]

variable [NoZeroSMulDivisors R S]

attribute [local instance] Ideal.Quotient.field

/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the prime
    factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
    over `R`, taken `mod I`.-/
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} := by
  -- Porting note: Lean needs to be reminded about this so it does not time out
  have : IsPrincipalIdealRing (R ⧸ I)[X] := inferInstance
  -- ⊢ ↑{J | J ∈ normalizedFactors (Ideal.map (algebraMap R S) I)} ≃ ↑{d | d ∈ norm …
  let f : S ⧸ map (algebraMap R S) I ≃+*
    (R ⧸ I)[X] ⧸ span {Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)} := by
    refine (quotAdjoinEquivQuotMap hx ?_).symm.trans
      (((Algebra.adjoin.powerBasis'
        hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans (quotEquivOfEq ?_))
    · exact NoZeroSMulDivisors.algebraMap_injective (Algebra.adjoin R {x}) S
    · rw [Algebra.adjoin.powerBasis'_minpoly_gen hx']
  refine (normalizedFactorsEquivOfQuotEquiv f ?_ ?_).trans ?_
  · rwa [Ne.def, map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective R S),
      ← Ne.def]
  · by_contra h
    -- ⊢ False
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) ≠ 0 from
      Polynomial.map_monic_ne_zero (minpoly.monic hx')) (span_singleton_eq_bot.mp h)
  · refine (normalizedFactorsEquivSpanNormalizedFactors ?_).symm
    -- ⊢ Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) ≠ 0
    exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
    -- 🎉 no goals
#align kummer_dedekind.normalized_factors_map_equiv_normalized_factors_min_poly_mk KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `FactorsEquiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) {J : Ideal S}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    multiplicity J (I.map (algebraMap R S)) =
      multiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk, Equiv.coe_trans, Function.comp_apply,
    multiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_multiplicity,
    normalizedFactorsEquivOfQuotEquiv_multiplicity_eq_multiplicity]
#align kummer_dedekind.multiplicity_factors_map_eq_multiplicity KummerDedekind.multiplicity_factors_map_eq_multiplicity

/-- The **Kummer-Dedekind Theorem**. -/
theorem normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach := by
  ext J
  -- ⊢ Multiset.count J (normalizedFactors (Ideal.map (algebraMap R S) I)) = Multis …
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalizedFactors (I.map (algebraMap R S));
  -- ⊢ Multiset.count J (normalizedFactors (Ideal.map (algebraMap R S) I)) = Multis …
  swap
  -- ⊢ Multiset.count J (normalizedFactors (Ideal.map (algebraMap R S) I)) = Multis …
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    -- ⊢ ¬∃ a, a ∈ Multiset.attach (normalizedFactors (Polynomial.map (Ideal.Quotient …
    simp only [Multiset.mem_attach, true_and_iff, not_exists]
    -- ⊢ ∀ (x_1 : ↑{d | d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) ( …
    rintro J' rfl
    -- ⊢ False
    exact
      hJ ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J').prop
  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity hI hI' hx hx' hJ
  -- ⊢ Multiset.count J (normalizedFactors (Ideal.map (algebraMap R S) I)) = Multis …
  rw [multiplicity_eq_count_normalizedFactors, multiplicity_eq_count_normalizedFactors,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hJ,
    UniqueFactorizationMonoid.normalize_normalized_factor, PartENat.natCast_inj] at this
  refine' this.trans _
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' :
    (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx') ⟨J, hJ⟩ = J'
  have : ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J' : Ideal S) =
      J :=
    by rw [← hJ', Equiv.symm_apply_apply _ _, Subtype.coe_mk]
  subst this
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [Multiset.count_map_eq_count' fun f =>
      ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f :
        Ideal S),
    Multiset.attach_count_eq_count_coe]
  · exact Subtype.coe_injective.comp (Equiv.injective _)
    -- 🎉 no goals
  · exact (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
    -- 🎉 no goals
  · exact irreducible_of_normalized_factor _
        (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
    -- 🎉 no goals
  · exact irreducible_of_normalized_factor _ hJ
    -- 🎉 no goals
  · rwa [← bot_eq_zero, Ne.def,
      map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective R S)]
#align kummer_dedekind.normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map

theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    (hf : Irreducible (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    Irreducible (I.map (algebraMap R S)) := by
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) ∈
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) :=
    by simp [normalizedFactors_irreducible hf]
  suffices ∃ y, normalizedFactors (I.map (algebraMap R S)) = {y} by
    obtain ⟨y, hy⟩ := this
    have h := normalizedFactors_prod (show I.map (algebraMap R S) ≠ 0 by
          rwa [← bot_eq_zero, Ne.def,
            map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective R S)])
    rw [associated_iff_eq, hy, Multiset.prod_singleton] at h
    rw [← h]
    exact
      irreducible_of_normalized_factor y
        (show y ∈ normalizedFactors (I.map (algebraMap R S)) by simp [hy])
  rw [normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx']
  -- ⊢ ∃ y, Multiset.map (fun f => ↑(↑(normalizedFactorsMapEquivNormalizedFactorsMi …
  use ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
        ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  -- ⊢ ∃ a, Multiset.attach (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I …
  use ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩
  -- ⊢ Multiset.attach (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (mi …
  refine ⟨?_, rfl⟩
  -- ⊢ Multiset.attach (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (mi …
  apply Multiset.map_injective Subtype.coe_injective
  -- ⊢ Multiset.map (fun a => ↑a) (Multiset.attach (normalizedFactors (Polynomial.m …
  rw [Multiset.attach_map_val, Multiset.map_singleton, Subtype.coe_mk]
  -- ⊢ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) = {↑n …
  exact normalizedFactors_irreducible hf
  -- 🎉 no goals
#align kummer_dedekind.ideal.irreducible_map_of_irreducible_minpoly KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly

end KummerDedekind
