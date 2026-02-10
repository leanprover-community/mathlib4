/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Paul Lezeau, Junyan Xu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

* `minpoly.isIntegrallyClosed_eq_field_fractions`: For integrally closed domains, the minimal
  polynomial over the ring is the same as the minimal polynomial over the fraction field.

* `minpoly.isIntegrallyClosed_dvd`: For integrally closed domains, the minimal polynomial divides
  any primitive polynomial that has the integral element as root.

* `IsIntegrallyClosed.Minpoly.unique`: The minimal polynomial of an element `x` is uniquely
  characterized by its defining property: if there is another monic polynomial of minimal degree
  that has `x` as a root, then this polynomial is equal to the minimal polynomial of `x`.

-/

@[expose] public section

open Polynomial Set Function minpoly Module

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
  refine (eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. Compared to `minpoly.isIntegrallyClosed_eq_field_fractions`,
this version is useful if the element is in a ring that is already a `K`-algebra. -/
theorem isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]
    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) := by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs, algebraMap_eq (IsFractionRing.injective S L)]

end

variable [IsIntegrallyClosed R] [IsDomain S] [IsTorsionFree R S]

/-- For integrally closed rings, the minimal polynomial divides any polynomial that has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions on `S`
  in exchange for stronger assumptions on `R`. -/
theorem isIntegrallyClosed_dvd {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p := by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs), modByMonic_eq_sub_mul_div]
    · refine dvd_sub (minpoly.dvd K (algebraMap S L s) ?_) ?_
      · rw [← map_aeval_eq_aeval_map, hp, map_zero]
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      apply dvd_mul_of_dvd_left
      rw [isIntegrallyClosed_eq_field_fractions K L hs]
    exact Monic.map _ (minpoly.monic hs)
  rw [isIntegrallyClosed_eq_field_fractions _ _ hs,
    map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (minpoly.monic hs)] at this
  rw [← modByMonic_eq_zero_iff_dvd (minpoly.monic hs)]
  exact Polynomial.eq_zero_of_dvd_of_degree_lt this (degree_modByMonic_lt p <| minpoly.monic hs)

theorem isIntegrallyClosed_dvd_iff {s : S} (hs : IsIntegral R s) (p : R[X]) :
    Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
  ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map_algebraMap] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩

theorem ker_eval {s : S} (hs : IsIntegral R s) :
    RingHom.ker ((Polynomial.aeval s).toRingHom : R[X] →+* S) =
    Ideal.span ({minpoly R s} : Set R[X]) := by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem IsIntegrallyClosed.degree_le_of_ne_zero {s : S} {p : R[X]}
    (hp0 : p ≠ 0) (hp : Polynomial.aeval s p = 0) : degree (minpoly R s) ≤ degree p := by
  by_cases! hs : ¬IsIntegral R s
  · simp [minpoly, hs]
  rw [degree_eq_natDegree (minpoly.ne_zero hs), degree_eq_natDegree hp0]
  norm_cast
  exact natDegree_le_of_dvd ((isIntegrallyClosed_dvd_iff hs _).mp hp) hp0

/-- If `x` is a root of an irreducible polynomial `p`, then `x` is integral
iff the leading coefficient of `p` is a unit. -/
theorem IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff {x : S} {p : R[X]}
    (hirr : Irreducible p) (hp : p.aeval x = 0) :
    IsIntegral R x ↔ IsUnit p.leadingCoeff where
  mp int_x := by
    obtain ⟨p, rfl⟩ := isIntegrallyClosed_dvd int_x hp
    rw [leadingCoeff_mul, monic int_x, one_mul]
    exact ((of_irreducible_mul hirr).resolve_left (not_isUnit R x)).map leadingCoeffHom
  mpr isUnit := by
    simpa [smul_smul] using (isIntegral_leadingCoeff_smul _ _ hp).smul ((isUnit.unit⁻¹ : Rˣ) : R)

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
  refine IsIntegrallyClosed.degree_le_of_ne_zero (s := s) hnz (by simp [hP]) |>.not_gt ?_
  refine degree_sub_lt ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leadingCoeff]

theorem IsIntegrallyClosed.unique_of_degree_le_degree_minpoly {s : S} {p : R[X]} (hmo : p.Monic)
    (hp : p.aeval s = 0) (pmin : p.degree ≤ (minpoly R s).degree) : p = minpoly R s :=
  IsIntegrallyClosed.minpoly.unique hmo hp fun _ qm hq ↦ pmin.trans <| min _ _ qm hq

theorem IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd {s : S} {p : R[X]} (hp : p.aeval s = 0)
    (h₀ : p ≠ 0) (pmin : ∀ q : R[X], q.Monic → q.aeval s = 0 → p.degree ≤ q.degree) :
    IsIntegral R s ↔ C p.leadingCoeff ∣ p := by
  refine ⟨fun hInt ↦ ?_, fun ⟨q, hMul⟩ ↦ minpoly.ne_zero_iff.mp ?_⟩
  · use minpoly R s
    have ⟨q, hMul⟩ := isIntegrallyClosed_dvd hInt hp
    suffices q.degree ≤ 0 by simp [degree_le_zero_iff.mp this ▸ hMul, minpoly.monic hInt, mul_comm]
    apply WithBot.le_of_add_le_add_left <| Polynomial.degree_ne_bot.mpr <| minpoly.ne_zero hInt
    convert pmin _ (minpoly.monic hInt) (minpoly.aeval ..)
    · rw [hMul, degree_mul]
    · rw [add_zero]
  · convert right_ne_zero_of_mul <| hMul ▸ h₀
    refine IsIntegrallyClosed.minpoly.unique ?_ ?_ ?_ |>.symm
    · have := hMul ▸ leadingCoeff_mul .. |>.symm
      simp only [leadingCoeff_C, ne_eq, leadingCoeff_eq_zero, h₀, not_false_eq_true, mul_eq_left₀]
        at this
      exact this
    · have := congrArg (Polynomial.aeval s) hMul
      simp only [hp, h₀, map_mul, aeval_C, zero_eq_mul, FaithfulSMul.algebraMap_eq_zero_iff,
        leadingCoeff_eq_zero, false_or] at this
      exact this
    · exact (hMul ▸ degree_C_mul <| by simp [h₀]) ▸ pmin

theorem prime_of_isIntegrallyClosed {x : S} (hx : IsIntegral R x) : Prime (minpoly R x) := by
  refine
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => ?_⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero h' h

lemma _root_.IsIntegrallyClosed.minpoly_smul {r : R} (hr : r ≠ 0) {s : S} (hs : IsIntegral R s) :
    minpoly R (r • s) = (minpoly R s).scaleRoots r := by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r),
    map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff]),
    ← minpoly.isIntegrallyClosed_eq_field_fractions K L hs]
  simp_rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R K L]
  refine eq_of_monic_of_associated (minpoly.monic ?_) ?_
    (associated_of_dvd_dvd (minpoly.dvd _ _ ?_) ?_)
  · refine isIntegral_algebraMap.mul (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · simpa [monic_scaleRoots_iff] using minpoly.monic
      (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)
  · rw [← Polynomial.scaleRoots_dvd_iff _ _ (r := (algebraMap R K r)⁻¹) (IsUnit.mk0 _ (by simpa)),
      ← scaleRoots_mul, mul_inv_cancel₀ (by simpa), scaleRoots_one]
    refine minpoly.dvd _ _ ?_
    nth_rw 1 [← inv_mul_cancel_left₀ (b := algebraMap S L s)
      (a := algebraMap K L (algebraMap R K r)) (by simpa), ← map_inv₀]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)

noncomputable section AdjoinRoot

open Algebra Polynomial AdjoinRoot

variable {x : S}

theorem ToAdjoin.injective (hx : IsIntegral R x) : Function.Injective (Minpoly.toAdjoin R x) := by
  refine (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => ?_
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  simpa [← Subalgebra.coe_eq_zero, isIntegrallyClosed_dvd_iff hx, ← aeval_def] using hP₁

/-- The algebra isomorphism `AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R x` -/
def equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R ({x} : Set S) :=
  AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩

@[simp]
theorem equivAdjoin_toAlgHom (hx : IsIntegral R x) : equivAdjoin hx = Minpoly.toAdjoin R x := rfl

@[simp]
theorem coe_equivAdjoin (hx : IsIntegral R x) : ⇑(equivAdjoin hx) = Minpoly.toAdjoin R x := rfl

@[deprecated (since := "2025-07-21")] alias equivAdjoin_apply := coe_equivAdjoin

/-- The `PowerBasis` of `adjoin R {x}` given by `x`. See `Algebra.adjoin.powerBasis` for a version
over a field. -/
def _root_.Algebra.adjoin.powerBasis' (hx : IsIntegral R x) :
    PowerBasis R (Algebra.adjoin R ({x} : Set S)) :=
  PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)

@[simp]
theorem _root_.Algebra.adjoin.powerBasis'_dim (hx : IsIntegral R x) :
    (Algebra.adjoin.powerBasis' hx).dim = (minpoly R x).natDegree := rfl

@[simp]
theorem _root_.Algebra.adjoin.powerBasis'_gen (hx : IsIntegral R x) :
    (adjoin.powerBasis' hx).gen = ⟨x, SetLike.mem_coe.1 <| subset_adjoin <| mem_singleton x⟩ := by
  rw [Algebra.adjoin.powerBasis', PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen, equivAdjoin,
    AlgEquiv.ofBijective_apply, Minpoly.toAdjoin, liftAlgHom_root]

/--
If `x` generates `S` over `R` and is integral over `R`, then it defines a power basis.
See `PowerBasis.ofAdjoinEqTop` for a version over a field.
-/
noncomputable def _root_.PowerBasis.ofAdjoinEqTop' {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) :
    PowerBasis R S :=
  (adjoin.powerBasis' hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

example {x : S} (B : PowerBasis R S)
    (hint : IsIntegral R x) (hx : B.gen ∈ Algebra.adjoin R {x}) :
    PowerBasis R S := by
  apply PowerBasis.ofAdjoinEqTop' hint
  exact PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx

@[deprecated "Use in combination with `PowerBasis.adjoin_eq_top_of_gen_mem_adjoin` to recover the \
  deprecated definition" (since := "2025-09-28")] alias _root_.PowerBasis.ofGenMemAdjoin' :=
  _root_.PowerBasis.ofAdjoinEqTop'

@[simp]
theorem _root_.PowerBasis.ofAdjoinEqTop'_dim {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) :
    (PowerBasis.ofAdjoinEqTop' hx hx').dim = (minpoly R x).natDegree := rfl

@[simp]
theorem _root_.PowerBasis.ofAdjoinEqTop'_gen {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) : (PowerBasis.ofAdjoinEqTop' hx hx').gen = x := by
  simp [PowerBasis.ofAdjoinEqTop']

@[deprecated "Use in combination with `PowerBasis.adjoin_eq_top_of_gen_mem_adjoin` to recover the \
  deprecated definition" (since := "2025-09-28")] alias _root_.PowerBasis.ofGenMemAdjoin'_dim :=
   _root_.PowerBasis.ofAdjoinEqTop'_dim

@[deprecated "Use in combination with `PowerBasis.adjoin_eq_top_of_gen_mem_adjoin` to recover the \
  deprecated definition" (since := "2025-09-28")] alias _root_.PowerBasis.ofGenMemAdjoin'_gen :=
  _root_.PowerBasis.ofAdjoinEqTop'_gen

end AdjoinRoot

section Subring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (A : Subring K) [IsIntegrallyClosed A] [IsFractionRing A K]

-- Implementation note: `inferInstance` does not work for these.
instance : Algebra A (integralClosure A L) := Subalgebra.algebra (integralClosure A L)
instance : SMul A (integralClosure A L) := Algebra.toSMul
instance : IsScalarTower A ((integralClosure A L)) L :=
  IsScalarTower.subalgebra' A L L (integralClosure A L)

/-- The minimal polynomial of `x : L` over `K` agrees with its minimal polynomial over the
integrally closed subring `A`. -/
theorem ofSubring (x : integralClosure A L) :
    Polynomial.map (algebraMap A K) (minpoly A x) = minpoly K (x : L) :=
  eq_comm.mpr (isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral A L x))

end Subring

end minpoly
