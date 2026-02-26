/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Lüroth's theorem

The goal of this file is to prove Lüroth's theorem, which says that for every
field `K`, every intermediate field between `K` and the rational function field
`K(X)` is either `K` or isomorphic to `K(X)` as an K-algebra. The proof depends
on the following lemma on degrees of rational functions:

Let `f` be a rational function, i.e. an element in the field `K(X)` (`RatFunc
K`). Let `p` be its numerator and `q` its denominator. Then the degree of the
field extension `K(X)/K(f)` equals the maximum of the degrees of `p` and `q`,
see `finrank_eq_max_natDegree`. Since `finrank` is defined to be zero when the
extension is infinite, this holds even when `f` is constant.

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Springer, 2003, Proposition 11.3.1.
- N. Jacobson, *Basic Algebra II: Second Edition*, 1989 (Dover edition 2009), Theorem 8.38.

-/

@[expose] public section

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin
open scoped Polynomial

variable {K : Type*} [Field K] (f : RatFunc K)

local notation "K[f]" => Algebra.adjoin K {(f : RatFunc K)}

theorem adjoin_X : K⟮(X : RatFunc K)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem adjoin_adjoin_X : K⟮f⟯⟮(X : RatFunc K)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), adjoin_simple_adjoin_simple, eq_top_iff]
  exact le_trans (le_of_eq adjoin_X.symm) (IntermediateField.adjoin.mono _ _ _ (by simp))

/-- The equivalence between `K⟮f⟯⟮X⟯` and `RatFunc K` as `K⟮f⟯`-algebras. -/
noncomputable def adjoinAdjoinXEquiv : K⟮f⟯⟮(X : RatFunc K)⟯ ≃ₐ[K⟮f⟯] RatFunc K :=
  (IntermediateField.equivOfEq (adjoin_adjoin_X f)).trans IntermediateField.topEquiv

/-- The minimal polynomial of `X` over `K⟮f⟯`. It is defined as `f.num - f * f.denom`, viewed
as a polynomial with coefficients in `A`, where `A` is a `K[f]`-algebra. -/
noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
theorem C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0 := by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]

theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : RatFunc K) = 0 := by
  simp only [Polynomial.aeval_sub, Polynomial.aeval_map_algebraMap, aeval_X_left_eq_algebraMap,
    map_mul, Polynomial.aeval_C, IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : RatFunc K)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((map_ne_zero C).mpr
    (Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

section FNeC

-- In this section, we assume `f` is not constant.
variable (hf : ¬∃ c, f = C c)
include hf

theorem isAlgebraic_adjoin_simple_X : IsAlgebraic K⟮f⟯ (X : RatFunc K) :=
   ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

theorem isAlgebraic_adjoin_simple_X' : Algebra.IsAlgebraic K⟮f⟯ (RatFunc K) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : RatFunc K)⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact f.adjoinAdjoinXEquiv.isAlgebraic

theorem natDegree_denom_le_natDegree_minpolyX :
    f.denom.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree :=
  Polynomial.le_natDegree_of_ne_zero fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem natDegree_num_le_natDegree_minpolyX :
    f.num.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree := by
  have f_ne_zero : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply Polynomial.le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_natDegree,
    Polynomial.coeff_C_mul, AddSubgroupClass.coe_sub, SubalgebraClass.coe_algebraMap,
    algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap, ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero, ← mul_right_inj' (inv_ne_zero f_ne_zero), ← mul_assoc, inv_mul_cancel₀ f_ne_zero,
    one_mul, ← eq_div_iff <| (map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero), ← inv_inj, inv_inv, ← map_div₀, ← map_inv₀] at H
  exact hf ⟨_, H⟩

omit hf in
theorem natDegree_minpolyX :
    (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree ≤ _ := Polynomial.natDegree_sub_le _ _
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C_mul fun H ↦
      hf ⟨0, by simpa [map_zero] using congr($(H).val)⟩,
      Polynomial.natDegree_map] at this
    exact this
  · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| Polynomial.le_natDegree_of_ne_zero
      fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem transcendental_of_ne_C : Transcendental K f := by
  intro H
  have := IntermediateField.isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K (RatFunc K) := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

theorem irreducible_minpolyX' : Irreducible (f.minpolyX K[f]) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [AlgEquiv.toRingEquiv_eq_coe, Polynomial.algebraMap_eq, Polynomial.mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, Polynomial.algEquivOfTranscendental_apply,
      Polynomial.map_sub, Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C, RingHom.coe_coe,
      Polynomial.aeval_X, φ, e]
    congr 2 <;> ext <;> simp
  rw [← φ_map, MulEquiv.irreducible_iff]
  have : φ = Polynomial.Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [Polynomial.X_mul_C, Polynomial.Bivariate.swap_apply, AlgHom.coe_comp,
      AlgHom.coe_restrictScalars', Polynomial.coe_aeval_eq_eval, Function.comp_apply,
      Polynomial.aeval_sub, Polynomial.aeval_C, Polynomial.algebraMap_def,
      Polynomial.coe_mapRingHom, map_mul, Polynomial.aeval_X, Polynomial.eval_sub,
      Polynomial.eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this, MulEquiv.irreducible_iff]
  convert Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
    ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm, Polynomial.X_mul_C, map_neg, neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

theorem irreducible_minpolyX : Irreducible (f.minpolyX K⟮f⟯) := by
  haveI : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := Polynomial.natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

end FNeC

theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ (RatFunc K) = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦  Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K (RatFunc K)]
    simp
  rw [← (adjoinAdjoinXEquiv f).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    Polynomial.natDegree_C_mul <| inv_ne_zero <| Polynomial.leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]

end RatFunc
