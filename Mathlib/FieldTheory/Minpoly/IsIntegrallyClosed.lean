/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Paul Lezeau, Junyan Xu
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.GaussLemma

#align_import field_theory.minpoly.is_integrally_closed from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

 * `minpoly.isIntegrallyClosed_eq_field_fractions`: For integrally closed domains, the minimal
    polynomial over the ring is the same as the minimal polynomial over the fraction field.

 * `minpoly.isIntegrallyClosed_dvd` : For integrally closed domains, the minimal polynomial divides
    any primitive polynomial that has the integral element as root.

 * `IsIntegrallyClosed.Minpoly.unique` : The minimal polynomial of an element `x` is
    uniquely characterized by its defining property: if there is another monic polynomial of minimal
    degree that has `x` as a root, then this polynomial is equal to the minimal polynomial of `x`.

-/


open scoped Classical Polynomial

open Polynomial Set Function minpoly

namespace minpoly

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]

section

variable (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [CommRing L] [Nontrivial L]
  [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]

variable [IsIntegrallyClosed R]

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. See `minpoly.isIntegrallyClosed_eq_field_fractions'` if
`S` is already a `K`-algebra. -/
theorem isIntegrallyClosed_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) :
    minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K) := by
  refine' (eq_of_irreducible_of_monic _ _ _).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _
#align minpoly.is_integrally_closed_eq_field_fractions minpoly.isIntegrallyClosed_eq_field_fractions

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. Compared to `minpoly.isIntegrallyClosed_eq_field_fractions`,
this version is useful if the element is in a ring that is already a `K`-algebra. -/
theorem isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]
    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) := by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs, algebraMap_eq (IsFractionRing.injective S L)]
#align minpoly.is_integrally_closed_eq_field_fractions' minpoly.isIntegrallyClosed_eq_field_fractions'

end

variable [IsDomain S] [NoZeroSMulDivisors R S]
variable [IsIntegrallyClosed R]

/-- For integrally closed rings, the minimal polynomial divides any polynomial that has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions on `S`
  in exchange for stronger assumptions on `R`. -/
theorem isIntegrallyClosed_dvd {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p := by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have := FractionRing.isScalarTower_liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs), modByMonic_eq_sub_mul_div]
    · refine' dvd_sub (minpoly.dvd K (algebraMap S L s) _) _
      · rw [← map_aeval_eq_aeval_map, hp, map_zero]
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      apply dvd_mul_of_dvd_left
      rw [isIntegrallyClosed_eq_field_fractions K L hs]
    exact Monic.map _ (minpoly.monic hs)
  rw [isIntegrallyClosed_eq_field_fractions _ _ hs,
    map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (minpoly.monic hs)] at this
  rw [← modByMonic_eq_zero_iff_dvd (minpoly.monic hs)]
  exact Polynomial.eq_zero_of_dvd_of_degree_lt this (degree_modByMonic_lt p <| minpoly.monic hs)
#align minpoly.is_integrally_closed_dvd minpoly.isIntegrallyClosed_dvd

theorem isIntegrallyClosed_dvd_iff {s : S} (hs : IsIntegral R s) (p : R[X]) :
    Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
  ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map, ← aeval_def] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩
#align minpoly.is_integrally_closed_dvd_iff minpoly.isIntegrallyClosed_dvd_iff

theorem ker_eval {s : S} (hs : IsIntegral R s) :
    RingHom.ker ((Polynomial.aeval s).toRingHom : R[X] →+* S) =
    Ideal.span ({minpoly R s} : Set R[X]) := by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]
#align minpoly.ker_eval minpoly.ker_eval

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem IsIntegrallyClosed.degree_le_of_ne_zero {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp0 : p ≠ 0) (hp : Polynomial.aeval s p = 0) : degree (minpoly R s) ≤ degree p := by
  rw [degree_eq_natDegree (minpoly.ne_zero hs), degree_eq_natDegree hp0]
  norm_cast
  exact natDegree_le_of_dvd ((isIntegrallyClosed_dvd_iff hs _).mp hp) hp0
#align minpoly.is_integrally_closed.degree_le_of_ne_zero minpoly.IsIntegrallyClosed.degree_le_of_ne_zero

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem _root_.IsIntegrallyClosed.minpoly.unique {s : S} {P : R[X]} (hmo : P.Monic)
    (hP : Polynomial.aeval s P = 0)
    (Pmin : ∀ Q : R[X], Q.Monic → Polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
    P = minpoly R s := by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  refine IsIntegrallyClosed.degree_le_of_ne_zero hs hnz (by simp [hP]) |>.not_lt ?_
  refine degree_sub_lt ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leadingCoeff]
#align minpoly.is_integrally_closed.minpoly.unique IsIntegrallyClosed.minpoly.unique

theorem prime_of_isIntegrallyClosed {x : S} (hx : IsIntegral R x) : Prime (minpoly R x) := by
  refine'
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => _⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero h' h
#align minpoly.prime_of_is_integrally_closed minpoly.prime_of_isIntegrallyClosed

noncomputable section AdjoinRoot

open Algebra Polynomial AdjoinRoot

variable {x : S}

theorem ToAdjoin.injective (hx : IsIntegral R x) : Function.Injective (Minpoly.toAdjoin R x) := by
  refine' (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => _
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  rwa [Minpoly.toAdjoin_apply', liftHom_mk, ← Subalgebra.coe_eq_zero, aeval_subalgebra_coe,
    isIntegrallyClosed_dvd_iff hx, ← AdjoinRoot.mk_eq_zero] at hP₁
#align minpoly.to_adjoin.injective minpoly.ToAdjoin.injective

/-- The algebra isomorphism `AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps!]
def equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R ({x} : Set S) :=
  AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩
#align minpoly.equiv_adjoin minpoly.equivAdjoin

/-- The `PowerBasis` of `adjoin R {x}` given by `x`. See `Algebra.adjoin.powerBasis` for a version
over a field. -/
def _root_.Algebra.adjoin.powerBasis' (hx : IsIntegral R x) :
    PowerBasis R (Algebra.adjoin R ({x} : Set S)) :=
  PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)
#align algebra.adjoin.power_basis' Algebra.adjoin.powerBasis'

@[simp]
theorem _root_.Algebra.adjoin.powerBasis'_dim (hx : IsIntegral R x) :
    (Algebra.adjoin.powerBasis' hx).dim = (minpoly R x).natDegree := rfl
#align algebra.adjoin.power_basis'_dim Algebra.adjoin.powerBasis'_dim

@[simp]
theorem _root_.Algebra.adjoin.powerBasis'_gen (hx : IsIntegral R x) :
    (adjoin.powerBasis' hx).gen = ⟨x, SetLike.mem_coe.1 <| subset_adjoin <| mem_singleton x⟩ := by
  rw [Algebra.adjoin.powerBasis', PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen, equivAdjoin,
    AlgEquiv.ofBijective_apply, Minpoly.toAdjoin, liftHom_root]
#align algebra.adjoin.power_basis'_gen Algebra.adjoin.powerBasis'_gen

/-- The power basis given by `x` if `B.gen ∈ adjoin R {x}`. -/
noncomputable def _root_.PowerBasis.ofGenMemAdjoin' (B : PowerBasis R S) (hint : IsIntegral R x)
    (hx : B.gen ∈ adjoin R ({x} : Set S)) : PowerBasis R S :=
  (Algebra.adjoin.powerBasis' hint).map <|
    (Subalgebra.equivOfEq _ _ <| PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
      Subalgebra.topEquiv
#align power_basis.of_gen_mem_adjoin' PowerBasis.ofGenMemAdjoin'

@[simp]
theorem _root_.PowerBasis.ofGenMemAdjoin'_dim (B : PowerBasis R S) (hint : IsIntegral R x)
    (hx : B.gen ∈ adjoin R ({x} : Set S)) :
    (B.ofGenMemAdjoin' hint hx).dim = (minpoly R x).natDegree := rfl
#align power_basis.of_gen_mem_adjoin'_dim PowerBasis.ofGenMemAdjoin'_dim

@[simp]
theorem _root_.PowerBasis.ofGenMemAdjoin'_gen (B : PowerBasis R S) (hint : IsIntegral R x)
    (hx : B.gen ∈ adjoin R ({x} : Set S)) :
    (B.ofGenMemAdjoin' hint hx).gen = x := by
  simp [PowerBasis.ofGenMemAdjoin']
#align power_basis.of_gen_mem_adjoin'_gen PowerBasis.ofGenMemAdjoin'_gen

end AdjoinRoot

end minpoly
