/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.Relrank

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

open IntermediateField algebraAdjoinAdjoin Polynomial

variable {K : Type*} [Field K] (f : RatFunc K)

local notation "K[f]" => Algebra.adjoin K {(f : RatFunc K)}

theorem adjoin_X : K⟮(X : RatFunc K)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem IntermediateField.adjoin_X (E : IntermediateField K (RatFunc K)) :
    E⟮(X : RatFunc K)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), restrictScalars_adjoin, eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (IntermediateField.adjoin.mono _ _ _ (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between `E⟮X⟯` and `RatFunc K` as `E`-algebras. -/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K (RatFunc K)) :
    E⟮(X : RatFunc K)⟯ ≃ₐ[E] RatFunc K :=
  (IntermediateField.equivOfEq (IntermediateField.adjoin_X E)).trans IntermediateField.topEquiv

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

set_option backward.isDefEq.respectTransparency false in
theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : RatFunc K) = 0 := by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

set_option backward.isDefEq.respectTransparency false in
theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : RatFunc K)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

set_option backward.isDefEq.respectTransparency false in
theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem isAlgebraic_adjoin_simple_X (hf : ¬∃ c, f = C c) : IsAlgebraic K⟮f⟯ (X : RatFunc K) :=
   ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

set_option backward.isDefEq.respectTransparency false in
theorem isAlgebraic_adjoin_simple_X' (hf : ¬∃ c, f = C c) :
    Algebra.IsAlgebraic K⟮f⟯ (RatFunc K) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : RatFunc K)⟯ :=
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

set_option backward.isDefEq.respectTransparency false in
theorem transcendental_of_ne_C (hf : ¬∃ c, f = C c) : Transcendental K f := by
  intro H
  have := IntermediateField.isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K (RatFunc K) := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

set_option backward.isDefEq.respectTransparency false in
theorem irreducible_minpolyX' (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX K[f]) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [AlgEquiv.toRingEquiv_eq_coe, algebraMap_eq, map_sub, mapEquiv_apply,
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ (RatFunc K) = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦  Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K (RatFunc K)]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    natDegree_C_mul <| inv_ne_zero <| leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]

set_option backward.isDefEq.respectTransparency false in
theorem IntermediateField.isAlgebraic_X (E : IntermediateField K (RatFunc K)) (hE : E ≠ ⊥) :
    IsAlgebraic E (X : RatFunc K) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

namespace Luroth

open Polynomial
open scoped Polynomial.Bivariate

variable {E : IntermediateField K (RatFunc K)}

set_option backward.isDefEq.respectTransparency false in
variable (E) in
/-- The minimal polynomial of `X` with coefficients in `E`. This is an auxiliary
definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev ψ : E[X] := minpoly E (X : RatFunc K)

set_option backward.isDefEq.respectTransparency false in
private lemma ψ_ne_zero (h : E ≠ ⊥) : ψ E ≠ 0 :=
  minpoly.ne_zero (IntermediateField.isAlgebraic_X E h).isIntegral

set_option backward.isDefEq.respectTransparency false in
private lemma ψ_monic (h : E ≠ ⊥) : (ψ E).Monic :=
  minpoly.monic (IntermediateField.isAlgebraic_X E h).isIntegral

set_option backward.isDefEq.respectTransparency false in
private lemma ψ_natDegree (h : E ≠ ⊥) : (ψ E).natDegree = Module.finrank E (RatFunc K) := by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq,
    adjoin.finrank (IntermediateField.isAlgebraic_X E h).isIntegral]

set_option backward.isDefEq.respectTransparency false in
private lemma exists_ψ_coeff_not_mem (h : E ≠ ⊥) :
    ∃ i, (ψ E).coeff i ∉ (algebraMap K E).range := by
  rw [← notMem_map_range]
  intro ⟨f, hf⟩
  rw [coe_mapRingHom] at hf
  refine transcendental_X (K := K) ⟨f, ?_, ?_⟩
  · apply (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K E)).mp
    exact hf ▸ ψ_ne_zero h
  · have := congr(aeval (X : RatFunc K) $(hf))
    rw [aeval_map_algebraMap, aeval_X_left_eq_algebraMap, minpoly.aeval,
      map_eq_zero_iff _ (algebraMap_injective K)] at this
    rw [this, aeval_zero]

/-- The index we will use to define `generator E` as a coefficient of `ψ`. -/
private noncomputable def generatorIndex (h : E ≠ ⊥) : ℕ :=
  (exists_ψ_coeff_not_mem h).choose

variable (E) in
open Classical in
/-- A choice of a generator for Lüroth's theorem, see `eq_adjoin_generator`. -/
@[no_expose] noncomputable def generator : RatFunc K :=
  if h : E = ⊥ then 0 else (ψ E).coeff (generatorIndex h)

lemma generator_eq_zero (h : E = ⊥) : generator E = 0 := by
  unfold generator
  rw [dif_pos h]

private lemma generator_eq_coeff (h : E ≠ ⊥) : generator E = (ψ E).coeff (generatorIndex h) := by
  unfold generator
  rw [dif_neg h]

lemma generator_mem : generator E ∈ E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h,]
    exact SetLike.coe_mem _

lemma generator_spec (h : E ≠ ⊥) : generator E ∉ (algebraMap K (RatFunc K)).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  apply (exists_ψ_coeff_not_mem h).choose_spec
  exact ⟨f, by ext; exact hf⟩

lemma generator_ne_C (h : E ≠ ⊥) : ¬ ∃ c, generator E = C c :=
  fun ⟨c, hc⟩ ↦ generator_spec h ⟨c, (by simpa using hc.symm)⟩

lemma transcendental_generator (h : E ≠ ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

lemma generator_ne_zero (h : E ≠ ⊥) : (generator E : RatFunc K) ≠ 0 :=
  fun H ↦ generator_ne_C h ⟨0, by simp [H]⟩

lemma adjoin_generator_le : K⟮generator E⟯ ≤ E :=
  adjoin_simple_le_iff.mpr generator_mem

@[no_expose] private noncomputable instance : Algebra K⟮generator E⟯ E :=
  (IntermediateField.inclusion adjoin_generator_le).toAlgebra

variable (E) in
/-- The integer normalization of `ψ` as a bivariate polynomial. This is an
auxiliary definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev Φ' : K[X][Y] :=
  IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((ψ E).map (algebraMap E (RatFunc K)))

private lemma Φ'_ne_zero (h : E ≠ ⊥) : Φ' E ≠ 0 :=
  IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (Polynomial.map_ne_zero (ψ_ne_zero h))

variable (E) in
/-- A polynomial `b` that satisfies `b * ψ = Φ'`. This is an auxiliary
definition for the proof of Lüroth's theorem. -/
private noncomputable def b : K[X] :=
  (IsLocalization.integerNormalization_spec (nonZeroDivisors K[X])
    ((ψ E).map (algebraMap E (RatFunc K)))).choose

private lemma b_ne_zero : b E ≠ 0 :=
  nonZeroDivisors.ne_zero <| (IsLocalization.integerNormalization_spec _
    ((ψ E).map (algebraMap ..))).choose_spec.1

private lemma Φ'_map :
    (Φ' E).map (algebraMap K[X] (RatFunc K)) = (b E) • (ψ E).map (algebraMap ..) :=
  (IsLocalization.integerNormalization_spec _ ((ψ E).map (algebraMap ..))).choose_spec.2

variable (E) in
open Classical in
/-- A rational function `c` that satisfies `c * ψ = Φ`. This is an auxiliary
definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev c : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (Φ' E).content)⁻¹ * (algebraMap K[X] (RatFunc K) (b E))

open Classical in
private lemma c_ne_zero (h : E ≠ ⊥) : c E ≠ 0 :=
  mul_ne_zero_iff.mpr ⟨inv_ne_zero <| (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr <|
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

variable (E) in
open Classical in
/-- The primitive part of `Φ'`. This is an auxiliary definition for the proof of
Lüroth's theorem. -/
private noncomputable abbrev Φ : K[X][Y] := (Φ' E).primPart

set_option backward.isDefEq.respectTransparency false in
private lemma C_c_mul_ψ (h : E ≠ ⊥) :
    Polynomial.C (c E) * (ψ E).map (algebraMap E (RatFunc K)) = (Φ E).map (algebraMap ..) := by
  classical
  rw [map_mul, mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← Φ'_map, eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀,  map_one, one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
    exact Φ'_ne_zero h

private lemma Φ_natDegree_eq_ψ_natDegree (h : E ≠ ⊥) : (Φ E).natDegree = (ψ E).natDegree := by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K), ← C_c_mul_ψ h,
    natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (ψ_ne_zero h)), natDegree_C,
    natDegree_map, zero_add]

set_option backward.isDefEq.respectTransparency false in
private lemma Φ_coeff_ψ_natDegree (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (ψ E).natDegree) = c E := by
  have := congr($(C_c_mul_ψ h).coeff (ψ E).natDegree)
  rw [coeff_C_mul, coeff_map, coeff_map, coeff_natDegree, IntermediateField.algebraMap_apply,
    ψ_monic h, OneMemClass.coe_one, mul_one] at this
  exact this.symm

private lemma c_denom (h : E ≠ ⊥) : (c E).denom = 1 := by
  rw [← Φ_coeff_ψ_natDegree h]
  exact denom_algebraMap _

set_option backward.isDefEq.respectTransparency false in
private lemma Φ_coeff_ψ_natDegree' (h : E ≠ ⊥) :
    (Φ E).coeff (ψ E).natDegree = (c E).num := by
  apply algebraMap_injective
  rw [Φ_coeff_ψ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

private lemma Φ_coeff_ψ_natDegree_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (ψ E).natDegree ≠ 0 := by
  rw [Φ_coeff_ψ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

set_option backward.isDefEq.respectTransparency false in
private lemma Φ_coeff_generatorIndex (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (generatorIndex h)) =
    algebraMap K[X] (RatFunc K) (c E).num * generator E := by
  have := congr($(C_c_mul_ψ h).coeff (generatorIndex h))
  rw [coeff_map, coeff_C_mul, coeff_map, IntermediateField.algebraMap_apply] at this
  rw [← num_div_denom (c E), c_denom h, map_one, div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

private lemma Φ_coeff_generatorIndex_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (generatorIndex h) ≠ 0 := by
  apply_fun algebraMap K[X] (RatFunc K)
  rw [map_zero, Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

set_option backward.isDefEq.respectTransparency false in
private lemma generator_denom_dvd_c_num (h : E ≠ ⊥) : (generator E).denom ∣ (c E).num := by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h,
    mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

private lemma Φ_ne_zero (h : E ≠ ⊥) : Φ E ≠ 0 := by
  intro H
  have := Φ_coeff_ψ_natDegree' h ▸ congr($(H).coeff (ψ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

set_option backward.isDefEq.respectTransparency false in
private lemma le_Φ_coeff_generatorIndex_natDegree (h : E ≠ ⊥) :
    (generator E).num.natDegree ≤ ((Φ E).coeff (generatorIndex h)).natDegree := by
  classical
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] (RatFunc K) (generator E).denom)
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc, div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero),
    ← map_mul, ← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero,
    natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  rw [Nat.eq_sub_of_add_eq this, add_comm, Nat.add_sub_assoc <|
    natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h)),
    le_add_iff_nonneg_right]
  exact zero_le _

private lemma le_Φ_coeff_natDegree_natDegree (h : E ≠ ⊥) :
    (generator E).denom.natDegree ≤ ((Φ E).coeff (ψ E).natDegree).natDegree := by
  rw [Φ_coeff_ψ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

private lemma le_swap_Φ_natDegree (h : E ≠ ⊥) :
    max (generator E).num.natDegree (generator E).denom.natDegree ≤
      (Bivariate.swap (Φ E)).natDegree := by
  rw [← sum_monomial_eq (Φ E), sum_def, map_sum]
  conv in (fun _ ↦ _) =>
    ext
    rw [Bivariate.swap_monomial, mul_comm, ← Polynomial.smul_eq_C_mul,
      ← monomial_one_right_eq_X_pow, ← Polynomial.algebraMap_eq]
  rw [natDegree_sum_eq_of_linearIndepOn _
    (coe_basisMonomials K ▸ (basisMonomials K).linearIndepOn (Φ E).support)]
  apply max_le
  · exact (le_Φ_coeff_generatorIndex_natDegree h).trans <|
      Finset.le_sup (f := fun i ↦ ((Φ E).coeff i).natDegree) <|
      mem_support_iff.mpr (Φ_coeff_generatorIndex_ne_zero h)
  · exact (le_Φ_coeff_natDegree_natDegree h).trans <|
      Finset.le_sup (f := fun i ↦ ((Φ E).coeff i).natDegree) <|
      mem_support_iff.mpr (Φ_coeff_ψ_natDegree_ne_zero h)

set_option backward.isDefEq.respectTransparency false in
private lemma ψ_dvd_generator_minpolyX :
    ψ E ∣ ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) := by
  apply minpoly.dvd
  rw [← aeval_eq_aeval_map rfl]
  exact (generator E).minpolyX_aeval_X

variable (E) in
/-- A polynomial `q` that satisfies `ψ * q = generator`. This is an auxiliary
definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev q : E[X] :=
  (ψ_dvd_generator_minpolyX (E := E)).choose

private lemma ψ_mul_q :
    ψ E * q E = ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) :=
  (ψ_dvd_generator_minpolyX (E := E)).choose_spec.symm

private lemma q_ne_zero (h : E ≠ ⊥) : q E ≠ 0 := right_ne_zero_of_mul <|
  ψ_mul_q (E := E) ▸ Polynomial.map_ne_zero <|
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

variable (E) in
/-- A polynomial `Q₀` with coefficients in `RatFunc K` that satisfies `Q * Φ = θ`.
This is an auxiliary definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev Q₀ : (RatFunc K)[X] :=
  Polynomial.C ((algebraMap K[X] (RatFunc K) (generator E).denom) / c E) *
    (q E).map (algebraMap E (RatFunc K))

private lemma Q₀_ne_zero (h : E ≠ ⊥) : Q₀ E ≠ 0 := by
  apply mul_ne_zero
  · apply C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

variable (E) in
/-- The bivariate polynomial `g(X) * f(Y) - f(X) * g(Y)`, where `f` and `g` are
the numerator and denominator of `generator`. This is an auxiliary definition
for the proof of Lüroth's theorem. -/
private noncomputable abbrev θ : K[X][Y] :=
  Polynomial.C (generator E).denom * (generator E).num.map Polynomial.C -
  Polynomial.C (generator E).num * (generator E).denom.map Polynomial.C

private lemma swap_θ : Polynomial.Bivariate.swap (θ E) = -(θ E) := by
  rw [map_sub, map_mul, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Bivariate.swap_C,
    Bivariate.swap_map_C]
  ring

private lemma θ_natDegree_le (h : E ≠ ⊥) :
    (θ E).natDegree ≤ max (generator E).num.natDegree (generator E).denom.natDegree := by
  convert natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

set_option backward.isDefEq.respectTransparency false in
private lemma Q₀_mul_Φ (h : E ≠ ⊥) :
    Q₀ E * (Φ E).map (algebraMap K[X] (RatFunc K)) = (θ E).map (algebraMap K[X] (RatFunc K)) := by
  rw [← C_c_mul_ψ h, mul_assoc]
  conv =>
    lhs; rhs
    rw [← mul_assoc]
    lhs
    rw [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h), mul_assoc,
    ← Polynomial.map_mul, mul_comm (q E) (ψ E), ψ_mul_q, Polynomial.map_map, Polynomial.map_sub,
    Polynomial.map_mul, map_C, RingHom.coe_comp, Function.comp_apply,
    IntermediateField.algebraMap_apply, Polynomial.map_map, Polynomial.map_map, mul_sub,
    ← mul_assoc, ← map_mul, (inclusion adjoin_generator_le).algebraMap_toAlgebra,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_inclusion, coe_algebraMap]
  conv => enter [1, 2, 1, 2, 2]; rw [← num_div_denom (generator E)]
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero), Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, Polynomial.map_map, Polynomial.map_map]
  rfl

private lemma Q₀_mem_lifts (h : E ≠ ⊥) : Q₀ E ∈ lifts (algebraMap K[X] (RatFunc K)) := by
  classical
  apply (Φ' E).isPrimitive_primPart.mul_map_mem_lifts_iff.mp
  rw [Q₀_mul_Φ h]
  exact ⟨_, rfl⟩

/-- A bivariate polynomial `Q₁` that satisfies `Q₁ * Φ = θ`. This is an
auxiliary definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev Q₁ (h : E ≠ ⊥) : K[X][Y] :=
  (Q₀_mem_lifts h).choose

private lemma map_Q₁ (h : E ≠ ⊥) : (Q₁ h).map (algebraMap K[X] (RatFunc K)) = Q₀ E :=
  (Q₀_mem_lifts h).choose_spec

private lemma Q₁_ne_zero (h : E ≠ ⊥) : Q₁ h ≠ 0 := by
  apply_fun Polynomial.map (algebraMap K[X] (RatFunc K))
  rw [map_Q₁, Polynomial.map_zero]
  exact Q₀_ne_zero h

private lemma Q₁_mul_Φ (h : E ≠ ⊥) : Q₁ h * Φ E = θ E := by
  apply_fun Polynomial.map (algebraMap K[X] (RatFunc K)) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul, map_Q₁, Q₀_mul_Φ h]

private lemma swap_Q₁_natDegree (h : E ≠ ⊥) : (Bivariate.swap (Q₁ h)).natDegree = 0 := by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  let m := max (generator E).num.natDegree (generator E).denom.natDegree
  have h₁ : (Bivariate.swap (θ E)).natDegree ≤ m := by
    rw [swap_θ, natDegree_neg]
    exact θ_natDegree_le h
  have h₂ : m ≤ (Bivariate.swap (Φ E)).natDegree := le_swap_Φ_natDegree h
  linarith

/-- A univariate polynomial `Q₂` that satisfies `Q₂ * Φ = θ`. This is an
auxiliary definition for the proof of Lüroth's theorem. -/
private noncomputable abbrev Q₂ (h : E ≠ ⊥) : K[X] := (Bivariate.swap (Q₁ h)).coeff 0

private lemma Q₂_map (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C = Q₁ h := by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [Bivariate.swap_swap_apply, Bivariate.swap_C] at this
  exact this.symm

private lemma Q₂_ne_zero (h : E ≠ ⊥) : Q₂ h ≠ 0 := by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero, Q₂_map]
  exact Q₁_ne_zero h

private lemma Q₂_mul_Φ (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C * Φ E = θ E := by
  rw [Q₂_map h, Q₁_mul_Φ h]

attribute [local instance] Polynomial.algebra in
private lemma Q₂_natDegree (h : E ≠ ⊥) : (Q₂ h).natDegree = 0 := by
  by_contra H
  apply (generator E).eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not, ← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (ne_of_not_ge H).symm
  rw [IsRoot.def, eval_map_algebraMap] at hα
  have eq := (Q₂_mul_Φ h).symm
  apply_fun aeval (Polynomial.C α) at eq
  rw [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, aeval_sub,
    aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
    ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
    ← Polynomial.coe_mapRingHom] at eq
  obtain ⟨aeval_num_ne_zero, aeval_denom_ne_zero⟩ :
      aeval α (generator E).num ≠ 0 ∧ aeval α (generator E).denom ≠ 0 := by
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, ?_⟩
      apply_fun Polynomial.C
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero) <|
        Polynomial.C_ne_zero.mpr H
    · refine ⟨?_, H⟩
      apply_fun Polynomial.C
      rw [map_zero, ← mul_ne_zero_iff_left (Polynomial.map_ne_zero (generator E).denom_ne_zero)]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))) <|
        Polynomial.C_ne_zero.mpr H
  have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom <|
    Polynomial.mapRingHom (algebraMap K F)
  constructor
  · rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K F) (generator E).num]
    apply natDegree_eq_zero_of_isUnit
    apply isCoprime.isUnit_of_dvd
    rw [← IsUnit.dvd_mul_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr aeval_num_ne_zero))]
    exact ⟨Polynomial.C ((aeval α) (generator E).denom), eq⟩
  · rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K F) (generator E).denom]
    apply natDegree_eq_zero_of_isUnit
    apply isCoprime.symm.isUnit_of_dvd
    rw [← IsUnit.dvd_mul_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr aeval_denom_ne_zero))]
    exact ⟨Polynomial.C ((aeval α) (generator E).num), eq.symm⟩

/-- A constant `Q₃` that satisfies `Q₃ * Φ = θ`. This is an auxiliary definition
for the proof of Lüroth's theorem. -/
private noncomputable abbrev Q₃ (h : E ≠ ⊥) : K := (Q₂ h).coeff 0

private lemma Q₃_map (h : E ≠ ⊥) : Polynomial.C (Q₃ h) = Q₂ h :=
  (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

private lemma Q₃_mul_Φ (h : E ≠ ⊥) : (Polynomial.C (Q₃ h)).map Polynomial.C * Φ E = θ E := by
  rw [Q₃_map h, Q₂_mul_Φ h]

private lemma Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Φ E).natDegree = (θ E).natDegree := by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rw [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this
  exact this

private lemma swap_Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Bivariate.swap (Φ E)).natDegree = (θ E).natDegree := by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rw [map_mul, Polynomial.map_C, Bivariate.swap_C_C,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- Lüroth's theorem. Any intermediate field between `K` and `RatFunc K` is
generated by a single element `generator E`. See also `transcendental_generator`
for the statement that the generator is transcendental if `E ≠ ⊥`. -/
theorem eq_adjoin_generator : E = K⟮(generator E : RatFunc K)⟯ := by
  by_cases h : E = ⊥
  · rwa [generator_eq_zero h, adjoin_zero]
  refine le_antisymm (relfinrank_eq_one_iff.mp ?_) adjoin_generator_le
  suffices (ψ E).natDegree = max (generator E).num.natDegree (generator E).denom.natDegree by
    refine (mul_eq_right₀ ?_).mp <| this ▸ (generator E).finrank_eq_max_natDegree ▸
      ψ_natDegree h ▸ relfinrank_mul_finrank_top (adjoin_generator_le (E := E))
    intro H
    exact generator_ne_C h ((eq_C_iff _).mpr (Nat.max_eq_zero_iff.mp H))
  rw [← Φ_natDegree_eq_ψ_natDegree h, Φ_natDegree_eq_θ_natDegree h]
  exact le_antisymm (θ_natDegree_le h) (swap_Φ_natDegree_eq_θ_natDegree h ▸ le_swap_Φ_natDegree h)

noncomputable def algEquiv (h : E ≠ ⊥) : RatFunc K ≃ₐ[K] E :=
  (algEquivOfTranscendental (generator E) (transcendental_of_ne_C _ (generator_ne_C h))).trans <|
    IntermediateField.equivOfEq eq_adjoin_generator.symm

end Luroth

end RatFunc
