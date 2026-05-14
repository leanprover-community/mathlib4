/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Intermediate Fields of Rational Function Fields

Results relating `IntermediateField` and `RatFunc`.
-/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial Algebra

@[expose] public section

variable (f : K⟮X⟯)

theorem adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem IntermediateField.adjoin_X (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), IntermediateField.restrictScalars_adjoin,
    _root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

/-- The equivalence between `E⟮X⟯` and `K⟮X⟯` as `E`-algebras. -/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯ :=
  (equivOfEq (adjoin_X E)).trans topEquiv

/-- The minimal polynomial of `X` over `K⟮f⟯`. It is defined as `f.num - f * f.denom`, viewed
as a polynomial with coefficients in `A`, where `A` is a `K[f]`-algebra. -/
noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
theorem C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0 := by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]

theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0 := by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

theorem isAlgebraic_adjoin_simple_X (hf : ¬∃ c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯) :=
   ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

theorem isAlgebraic_adjoin_simple_X' (hf : ¬∃ c, f = C c) :
    Algebra.IsAlgebraic K⟮f⟯ K⟮X⟯ := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : K⟮X⟯)⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

theorem natDegree_denom_le_natDegree_minpolyX (hf : ¬∃ c, f = C c) :
    f.denom.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree :=
  le_natDegree_of_ne_zero fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

set_option backward.isDefEq.respectTransparency false in
theorem natDegree_num_le_natDegree_minpolyX (hf : ¬∃ c, f = C c) :
    f.num.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree := by
  have f_ne_zero : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, AddSubgroupClass.coe_sub,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap,
    ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero, ← mul_right_inj' (inv_ne_zero f_ne_zero), ← mul_assoc, inv_mul_cancel₀ f_ne_zero,
    one_mul, ← eq_div_iff <| (_root_.map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero), ← inv_inj, inv_inv, ← map_div₀, ← map_inv₀] at H
  exact hf ⟨_, H⟩

theorem natDegree_minpolyX :
    (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree ≤ _ := natDegree_sub_le _ _
    rw [natDegree_map, natDegree_C_mul fun H ↦ hf ⟨0, by simpa [map_zero] using congr($(H).val)⟩,
      natDegree_map] at this
    exact this
  · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| le_natDegree_of_ne_zero
      fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem transcendental_of_ne_C (hf : ¬∃ c, f = C c) : Transcendental K f := by
  intro H
  have := isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K K⟮X⟯ := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

theorem irreducible_minpolyX' (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX K[f]) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [algebraMap_eq, map_sub, mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, algEquivOfTranscendental_coe, Polynomial.map_map, map_mul,
      map_C, RingHom.coe_coe, aeval_X, e, φ]
    congr 2 <;> ext <;> simp
  rw [← φ_map, MulEquiv.irreducible_iff]
  have : φ = Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [X_mul_C, Bivariate.swap_apply, aevalAeval, aevalAevalEquiv, Equiv.coe_fn_mk,
      AlgHom.coe_comp, AlgHom.coe_restrictScalars', coe_aeval_eq_eval, Function.comp_apply,
      aeval_sub, aeval_C, algebraMap_def, coe_mapRingHom, map_mul, aeval_X, eval_sub,
      eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this, MulEquiv.irreducible_iff]
  convert irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
    ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm, X_mul_C, map_neg, neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

theorem irreducible_minpolyX (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX K⟮f⟯) := by
  haveI : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦ Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K K⟮X⟯]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    natDegree_C_mul <| inv_ne_zero <| leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]

theorem IntermediateField.isAlgebraic_X {E : IntermediateField K K⟮X⟯} (hE : E ≠ ⊥) :
    IsAlgebraic E (X : K⟮X⟯) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

end

end RatFunc
