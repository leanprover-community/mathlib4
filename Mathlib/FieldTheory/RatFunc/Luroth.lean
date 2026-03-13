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

This file proves Lüroth's theorem, which says that for every field `K`, every
intermediate field between `K` and the rational function field `K⟮X⟯` is either
`K` or isomorphic to `K(X)` as an K-algebra, see `Luroth.algEquiv`. The proof
depends on the following lemma on degrees of rational functions:

Let `f` be a rational function, i.e. an element in the field `K⟮X⟯`.
Let `p` be its numerator and `q` its denominator. Then the degree of the
field extension `K⟮X⟯/K⟮f⟯` equals the maximum of the degrees of `p` and `q`,
see `finrank_eq_max_natDegree`. Since `finrank` is defined to be zero when the
extension is infinite, this holds even when `f` is constant.

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- [P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*][cohn_2003], Theorem 11.3.4
- [N. Jacobson, *Basic Algebra II: Second Edition*][jacobson1989], Theorem 8.38

-/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial

@[expose] public section

variable (f : K⟮X⟯)

local notation "K[f]" => Algebra.adjoin K {(f : K⟮X⟯)}

theorem adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem IntermediateField.adjoin_X (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), restrictScalars_adjoin, eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (IntermediateField.adjoin.mono _ _ _ (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between `E⟮X⟯` and `K⟮X⟯` as `E`-algebras. -/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯ :=
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
theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0 := by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

set_option backward.isDefEq.respectTransparency false in
theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

set_option backward.isDefEq.respectTransparency false in
theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem isAlgebraic_adjoin_simple_X (hf : ¬∃ c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯) :=
   ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
theorem transcendental_of_ne_C (hf : ¬∃ c, f = C c) : Transcendental K f := by
  intro H
  have := IntermediateField.isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K K⟮X⟯ := by infer_instance
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
    Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦  Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K K⟮X⟯]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    natDegree_C_mul <| inv_ne_zero <| leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]

set_option backward.isDefEq.respectTransparency false in
theorem IntermediateField.isAlgebraic_X {E : IntermediateField K K⟮X⟯} (hE : E ≠ ⊥) :
    IsAlgebraic E (X : K⟮X⟯) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

end

namespace Luroth
noncomputable section

open scoped Polynomial.Bivariate

variable {E : IntermediateField K K⟮X⟯}

-- The proof of Lüroth's theorem begins here. We follow the approach from
-- [Cohn, Basic Algebra: Groups, Rings and Fields][cohn_2003].

set_option backward.isDefEq.respectTransparency false in
variable (E) in
/-- The minimal polynomial of `X` with coefficients in `E`. -/
abbrev φ : E[X] := minpoly E (X : K⟮X⟯)

set_option backward.isDefEq.respectTransparency false in
lemma φ_ne_zero (h : E ≠ ⊥) : φ E ≠ 0 :=
  minpoly.ne_zero (IntermediateField.isAlgebraic_X h).isIntegral

set_option backward.isDefEq.respectTransparency false in
lemma φ_monic (h : E ≠ ⊥) : (φ E).Monic :=
  minpoly.monic (IntermediateField.isAlgebraic_X h).isIntegral

set_option backward.isDefEq.respectTransparency false in
lemma φ_natDegree (h : E ≠ ⊥) : (φ E).natDegree = Module.finrank E K⟮X⟯ := by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq,
    adjoin.finrank (IntermediateField.isAlgebraic_X h).isIntegral]

set_option backward.isDefEq.respectTransparency false in
/-- Since `X` is transcendental over `K`, not all coefficients of `φ` can be in `K`. -/
lemma exists_φ_coeff_not_mem (h : E ≠ ⊥) :
    ∃ i, (φ E).coeff i ∉ (algebraMap K E).range := by
  rw [← notMem_map_range]
  intro ⟨f, hf⟩
  rw [coe_mapRingHom] at hf
  refine transcendental_X ⟨f, ?_, ?_⟩
  · apply (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K E)).mp
    exact hf ▸ φ_ne_zero h
  · simpa using congr(aeval (X : K⟮X⟯) $(hf))

/-- A choice of coefficient index `i` such that `φ.coeff i` is not in `K`. -/
def generatorIndex (h : E ≠ ⊥) : ℕ :=
  (exists_φ_coeff_not_mem h).choose

variable (E) in
open Classical in
/-- A choice of a generator for Lüroth's theorem, see `Luroth.eq_adjoin_generator`. -/
public def generator : K⟮X⟯ :=
  if h : E = ⊥ then 0 else (φ E).coeff (generatorIndex h)

public lemma generator_eq_zero (h : E = ⊥) : generator E = 0 :=
  dif_pos h

lemma generator_eq_coeff (h : E ≠ ⊥) : generator E = (φ E).coeff (generatorIndex h) :=
  dif_neg h

public lemma generator_mem : generator E ∈ E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h,]
    exact SetLike.coe_mem _

public lemma generator_spec (h : E ≠ ⊥) : generator E ∉ (algebraMap K K⟮X⟯).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  exact (exists_φ_coeff_not_mem h).choose_spec ⟨f, by ext; exact hf⟩

public lemma generator_ne_C (h : E ≠ ⊥) : ¬ ∃ c, generator E = C c :=
  fun ⟨c, hc⟩ ↦ generator_spec h ⟨c, (by simpa using hc.symm)⟩

public lemma transcendental_generator (h : E ≠ ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

public lemma generator_ne_zero (h : E ≠ ⊥) : generator E ≠ 0 :=
  fun H ↦ generator_ne_C h ⟨0, by simp [H]⟩

public lemma adjoin_generator_le : K⟮generator E⟯ ≤ E :=
  adjoin_simple_le_iff.mpr generator_mem

variable (E) in
/-- The numerator of the generator. -/
abbrev f : K[X] := (generator E).num

variable (E) in
/-- The denominator of the generator. -/
abbrev g : K[X] := generator E |>.denom

-- The next step is to define a bivariate polynomial `Φ`, which is a multiple of `φ`.
-- Cohn does this my "multiplying with the lowest common denominator". In this formalisation,
-- we first define `Φ'` as any integer multiple of `φ`, and then set `Φ` to be its
-- primitive part.

variable (E) in
/-- The integer normalization of `φ` as a bivariate polynomial. -/
abbrev Φ' : K[X][Y] :=
  IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((φ E).map (algebraMap E K⟮X⟯))

lemma Φ'_ne_zero (h : E ≠ ⊥) : Φ' E ≠ 0 :=
  IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (map_ne_zero (φ_ne_zero h))

variable (E) in
/-- A polynomial `b` that satisfies `b * φ = Φ'`. -/
def b : K[X] :=
  (IsLocalization.integerNormalization_spec (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E K⟮X⟯))).choose

lemma b_ne_zero : b E ≠ 0 :=
  nonZeroDivisors.ne_zero <| (IsLocalization.integerNormalization_spec _
    ((φ E).map (algebraMap ..))).choose_spec.1

lemma Φ'_map :
    (Φ' E).map (algebraMap K[X] K⟮X⟯) = (b E) • (φ E).map (algebraMap ..) :=
  (IsLocalization.integerNormalization_spec _ ((φ E).map (algebraMap ..))).choose_spec.2

variable (E) in
open Classical in
/-- A rational function `c` that satisfies `c * φ = Φ`. This is `ν₀(x)` in Cohn's notation. -/
abbrev c : K⟮X⟯ :=
  (algebraMap K[X] K⟮X⟯ (Φ' E).content)⁻¹ * (algebraMap K[X] K⟮X⟯ (b E))

open Classical in
lemma c_ne_zero (h : E ≠ ⊥) : c E ≠ 0 :=
  mul_ne_zero_iff.mpr ⟨inv_ne_zero <| (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr <|
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

variable (E) in
open Classical in
/-- The primitive part of `Φ'`. -/
abbrev Φ : K[X][Y] := (Φ' E).primPart

set_option backward.isDefEq.respectTransparency false in
/-- We have `c * φ = Φ` as polynomials with coefficients in `Ratfunc K`. See Equation
  (11.3.5) in Cohn's proof. -/
lemma C_c_mul_φ (h : E ≠ ⊥) :
    Polynomial.C (c E) * (φ E).map (algebraMap E K⟮X⟯) = (Φ E).map (algebraMap ..) := by
  classical
  rw [map_mul, mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← Φ'_map, eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀,  map_one, one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
    exact Φ'_ne_zero h

lemma Φ_natDegree_eq_φ_natDegree (h : E ≠ ⊥) : (Φ E).natDegree = (φ E).natDegree := by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K), ← C_c_mul_φ h,
    natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h)), natDegree_C,
    natDegree_map, zero_add]

set_option backward.isDefEq.respectTransparency false in
lemma Φ_coeff_φ_natDegree (h : E ≠ ⊥) :
    algebraMap K[X] K⟮X⟯ ((Φ E).coeff (φ E).natDegree) = c E := by
  have := congr($(C_c_mul_φ h).coeff (φ E).natDegree)
  rw [coeff_C_mul, coeff_map, coeff_map, coeff_natDegree, IntermediateField.algebraMap_apply,
    φ_monic h, OneMemClass.coe_one, mul_one] at this
  exact this.symm

lemma c_denom (h : E ≠ ⊥) : (c E).denom = 1 := by
  rw [← Φ_coeff_φ_natDegree h]
  exact denom_algebraMap _

lemma Φ_coeff_φ_natDegree' (h : E ≠ ⊥) :
    (Φ E).coeff (φ E).natDegree = (c E).num := by
  apply algebraMap_injective
  rw [Φ_coeff_φ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

lemma Φ_coeff_φ_natDegree_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (φ E).natDegree ≠ 0 := by
  rw [Φ_coeff_φ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

set_option backward.isDefEq.respectTransparency false in
lemma Φ_coeff_generatorIndex (h : E ≠ ⊥) :
    algebraMap K[X] K⟮X⟯ ((Φ E).coeff (generatorIndex h)) =
    algebraMap K[X] K⟮X⟯ (c E).num * generator E := by
  have := congr($(C_c_mul_φ h).coeff (generatorIndex h))
  rw [coeff_map, coeff_C_mul, coeff_map, IntermediateField.algebraMap_apply,
    ← num_div_denom (c E), c_denom h, map_one, div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

lemma Φ_coeff_generatorIndex_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (generatorIndex h) ≠ 0 := by
  apply_fun algebraMap K[X] K⟮X⟯
  rw [map_zero, Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

lemma generator_denom_dvd_c_num (h : E ≠ ⊥) : (g E) ∣ (c E).num := by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h,
    mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

lemma Φ_ne_zero (h : E ≠ ⊥) : Φ E ≠ 0 := by
  intro H
  have := Φ_coeff_φ_natDegree' h ▸ congr($(H).coeff (φ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

-- Next, we show that `Φ` has degree at least `m := max(deg(f), deg(g))` in `x`, where
-- `f` and `g` are the numerator and denominator of the `generator`. Cohn mentions
-- this right after Equation (11.3.8). To prove it, we show that the leading coefficient
-- `ν₀(x)` has degree at least `deg(f)`, while `νᵢ(x)` (our chosen coefficient index) has
-- degree at least `deg(g)`. The claim then follows from the fact that the monomials `X ^ i`
-- are linearly independent, see `le_swap_Φ_natDegree`.

lemma le_Φ_coeff_generatorIndex_natDegree (h : E ≠ ⊥) :
    (f E).natDegree ≤ ((Φ E).coeff (generatorIndex h)).natDegree := by
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] K⟮X⟯ (g E))
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc, div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero),
    ← map_mul, ← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero,
    natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  grind [natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))]

lemma le_Φ_coeff_natDegree_natDegree (h : E ≠ ⊥) :
    (g E).natDegree ≤ ((Φ E).coeff (φ E).natDegree).natDegree := by
  rw [Φ_coeff_φ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

variable (E) in
/-- The height of `generator E`. -/
abbrev m : ℕ := max (f E).natDegree (g E).natDegree

lemma m_le_swap_Φ_natDegree (h : E ≠ ⊥) :
    m E ≤ (Bivariate.swap (Φ E)).natDegree := by
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
      mem_support_iff.mpr (Φ_coeff_φ_natDegree_ne_zero h)

instance : Algebra K⟮generator E⟯ E :=
  (IntermediateField.inclusion adjoin_generator_le).toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Since `minpolyX` of our `generator` annihilates `X`, the minimal polynomial `φ`
must divide it. -/
lemma φ_dvd_generator_minpolyX :
    φ E ∣ ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) := by
  apply minpoly.dvd
  rw [← aeval_eq_aeval_map rfl]
  exact (generator E).minpolyX_aeval_X

variable (E) in
/-- A polynomial `q` that satisfies `φ * q = (generator E).minpolyX`. -/
abbrev q : E[X] := φ_dvd_generator_minpolyX.choose

lemma φ_mul_q :
    φ E * q E = ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) :=
  φ_dvd_generator_minpolyX.choose_spec.symm

lemma q_ne_zero (h : E ≠ ⊥) : q E ≠ 0 := right_ne_zero_of_mul <|
  φ_mul_q (E := E) ▸ Polynomial.map_ne_zero <|
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

-- The next series of definitions concerns the polynomial `Q` in Cohn's proof.
-- A priori, it will be a polynomial with coefficients in `K⟮X⟯`, which we call `Q₀`.
-- We then show that `Q₀` is also a polynomial in the other variable, hence we get
-- a bivariate polynomial `Q₁`. Then we show that it is independent of `X`, hence we may
-- replace it by a univariate polynomial `Q₂`. Finally, we prove that it is also independent
-- of `x`, hence we replace it by a constant `Q₃`.

variable (E) in
/-- A polynomial `Q₀` with coefficients in `K⟮X⟯` that satisfies `Q₀ * Φ = θ`. -/
abbrev Q₀ : K⟮X⟯[X] :=
  Polynomial.C ((algebraMap K[X] K⟮X⟯ (g E)) / c E) * (q E).map (algebraMap E K⟮X⟯)

lemma Q₀_ne_zero (h : E ≠ ⊥) : Q₀ E ≠ 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

variable (E) in
/-- The bivariate polynomial `g(X) * f(Y) - f(X) * g(Y)`, where `f` and `g` are
the numerator and denominator of `generator`. This is an auxiliary definition
for the proof of Lüroth's theorem. -/
abbrev θ : K[X][Y] :=
  Polynomial.C (g E) * (f E).map Polynomial.C - Polynomial.C (f E) * (g E).map Polynomial.C

lemma swap_θ : Bivariate.swap (θ E) = -(θ E) := by
  rw [map_sub, map_mul, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Bivariate.swap_C,
    Bivariate.swap_map_C]
  ring

lemma θ_natDegree_le (h : E ≠ ⊥) : (θ E).natDegree ≤ m E := by
  convert natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

set_option backward.isDefEq.respectTransparency false in
/-- Equation (11.3.8) from Cohns proof, viewed as an equation of polynomials with coefficients
in `K⟮X⟯`. -/
lemma Q₀_mul_Φ (h : E ≠ ⊥) :
    Q₀ E * (Φ E).map (algebraMap K[X] K⟮X⟯) = (θ E).map (algebraMap K[X] K⟮X⟯) := by
  suffices
    Polynomial.C ((algebraMap K[X] K⟮X⟯) (g E)) * (q E).map (algebraMap (↥E) K⟮X⟯) *
       (φ E).map (algebraMap (↥E) K⟮X⟯) = (θ E).map (algebraMap K[X] K⟮X⟯) by
    rw [← C_c_mul_φ h, mul_assoc, ← mul_assoc _ (Polynomial.C (c E)) _,
      mul_comm _ (Polynomial.C (c E))]
    simpa only [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h)] using this
  rw [mul_assoc, ← Polynomial.map_mul, mul_comm (q E) (φ E), φ_mul_q, Polynomial.map_map,
    Polynomial.map_sub, Polynomial.map_mul, map_C, RingHom.coe_comp, Function.comp_apply,
    IntermediateField.algebraMap_apply, Polynomial.map_map, Polynomial.map_map, mul_sub,
    ← mul_assoc, ← map_mul, (inclusion adjoin_generator_le).algebraMap_toAlgebra,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_inclusion, coe_algebraMap]
  conv => enter [1, 2, 1, 2, 2]; rw [← num_div_denom (generator E)]
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero), Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, Polynomial.map_map, Polynomial.map_map]
  rfl

lemma Q₀_mem_lifts (h : E ≠ ⊥) : Q₀ E ∈ lifts (algebraMap K[X] K⟮X⟯) := by
  classical
  apply (Φ' E).isPrimitive_primPart.mul_map_mem_lifts_iff.mp
  rw [Q₀_mul_Φ h]
  exact ⟨_, rfl⟩

/-- A bivariate polynomial `Q₁` that satisfies `Q₁ * Φ = θ`. -/
abbrev Q₁ (h : E ≠ ⊥) : K[X][Y] := (Q₀_mem_lifts h).choose

lemma map_Q₁ (h : E ≠ ⊥) : (Q₁ h).map (algebraMap K[X] K⟮X⟯) = Q₀ E :=
  (Q₀_mem_lifts h).choose_spec

lemma Q₁_ne_zero (h : E ≠ ⊥) : Q₁ h ≠ 0 := by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯)
  rw [map_Q₁, Polynomial.map_zero]
  exact Q₀_ne_zero h

/-- Equation (11.3.8) from Cohns proof, viewed as an equation of bivariate polynomials. -/
lemma Q₁_mul_Φ (h : E ≠ ⊥) : Q₁ h * Φ E = θ E := by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul, map_Q₁, Q₀_mul_Φ h]

lemma swap_Q₁_natDegree (h : E ≠ ⊥) : (Bivariate.swap (Q₁ h)).natDegree = 0 := by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  have h₁ : (Bivariate.swap (θ E)).natDegree ≤ m E := by
    rw [swap_θ, natDegree_neg]
    exact θ_natDegree_le h
  grind [m_le_swap_Φ_natDegree h]

/-- A univariate polynomial `Q₂` that satisfies `Q₂ * Φ = θ`. -/
abbrev Q₂ (h : E ≠ ⊥) : K[X] := (Bivariate.swap (Q₁ h)).coeff 0

lemma Q₂_map (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C = Q₁ h := by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [Bivariate.swap_swap_apply, Bivariate.swap_C] at this
  exact this.symm

lemma Q₂_ne_zero (h : E ≠ ⊥) : Q₂ h ≠ 0 := by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero, Q₂_map]
  exact Q₁_ne_zero h

/-- Equation (11.3.8) from Cohns proof, where we view `Q` as a univariate polynomial. -/
lemma Q₂_mul_Φ (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C * Φ E = θ E := by
  rw [Q₂_map h, Q₁_mul_Φ h]

attribute [local instance] Polynomial.algebra in
lemma Q₂_natDegree (h : E ≠ ⊥) : (Q₂ h).natDegree = 0 := by
  -- We have f(X)*g(Y) - g(X)*f(Y) = Q₂(X) * Φ
  -- Assume Q₂ has positive degree, take a root in an algebraic extension
  by_contra H
  apply (generator E).eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not, ← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (ne_of_not_ge H).symm
  -- Evaluate at the root, get that f(α)*g(Y) = g(α)*f(Y)
  rw [IsRoot.def, eval_map_algebraMap] at hα
  have eq :
      (Polynomial.mapRingHom (algebraMap K F)) (g E) * Polynomial.C ((aeval α) (f E)) =
      (Polynomial.mapRingHom (algebraMap K F)) (f E) * Polynomial.C ((aeval α) (g E)) := by
    have := congr(aeval (Polynomial.C α) $(Q₂_mul_Φ h)).symm
    rwa [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, aeval_sub,
      aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
      ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
      ← Polynomial.coe_mapRingHom] at this
  obtain ⟨isUnit₁, isUnit₂⟩ :
      IsUnit (Polynomial.C <| aeval α (f E)) ∧ IsUnit (Polynomial.C <| aeval α (g E)) := by
    rw [Polynomial.isUnit_C, isUnit_iff_ne_zero, Polynomial.isUnit_C, isUnit_iff_ne_zero]
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, Polynomial.C_injective.ne_iff.mp ?_⟩
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero) <|
        Polynomial.C_ne_zero.mpr H
    · refine ⟨Polynomial.C_injective.ne_iff.mp ?_, H⟩
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero (generator E).denom_ne_zero]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))) <|
        Polynomial.C_ne_zero.mpr H
  -- obtain contradiction because f and g are coprime
  have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom <|
    Polynomial.mapRingHom (algebraMap K F)
  have : Associated ((f E).mapRingHom (algebraMap K F)) ((g E).mapRingHom (algebraMap K F)) := by
    rw [← associated_mul_isUnit_left_iff isUnit₂, Associated.comm]
    exact ⟨isUnit₁.unit, by simpa⟩
  have := isCoprime.isUnit_of_associated this
  exact ⟨by simpa using (natDegree_eq_zero_of_isUnit this.1),
    by simpa using (natDegree_eq_zero_of_isUnit this.2)⟩

/-- A constant `Q₃` that satisfies `Q₃ * Φ = θ`. -/
abbrev Q₃ (h : E ≠ ⊥) : K := (Q₂ h).coeff 0

lemma Q₃_map (h : E ≠ ⊥) : Polynomial.C (Q₃ h) = Q₂ h :=
  (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

/-- Equation (11.3.8) from Cohns proof, where we view `Q` as a constant. -/
lemma Q₃_mul_Φ (h : E ≠ ⊥) : (Polynomial.C (Q₃ h)).map Polynomial.C * Φ E = θ E := by
  rw [Q₃_map h, Q₂_mul_Φ h]

lemma Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Φ E).natDegree = (θ E).natDegree := by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rwa [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this

lemma swap_Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Bivariate.swap (Φ E)).natDegree = (θ E).natDegree := by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rwa [map_mul, Polynomial.map_C, Bivariate.swap_C_C,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this

/-- Lüroth's theorem. Any intermediate field between `K` and `K⟮X⟯` is
generated by a single element `generator E`. See also `transcendental_generator`
for the statement that the generator is transcendental if `E ≠ ⊥`. -/
public theorem eq_adjoin_generator : E = K⟮generator E⟯ := by
  by_cases h : E = ⊥
  · rwa [generator_eq_zero h, adjoin_zero]
  refine le_antisymm (relfinrank_eq_one_iff.mp ?_) adjoin_generator_le
  suffices (φ E).natDegree = m E by
    refine (mul_eq_right₀ ?_).mp <| this ▸ (generator E).finrank_eq_max_natDegree ▸
      φ_natDegree h ▸ relfinrank_mul_finrank_top (adjoin_generator_le (E := E))
    intro H
    exact generator_ne_C h ((eq_C_iff _).mpr (Nat.max_eq_zero_iff.mp H))
  rw [← Φ_natDegree_eq_φ_natDegree h, Φ_natDegree_eq_θ_natDegree h]
  exact le_antisymm (θ_natDegree_le h) (swap_Φ_natDegree_eq_θ_natDegree h ▸ m_le_swap_Φ_natDegree h)

/-- The `K`-algebra equivalence between `K⟮X⟯` and an intermediate field `E` given
by sending `X` to `generator E`. See also `Luroth.eq_adjoin_generator`. -/
public def algEquiv (h : E ≠ ⊥) : K⟮X⟯ ≃ₐ[K] E :=
  (algEquivOfTranscendental (generator E) (transcendental_of_ne_C _ (generator_ne_C h))).trans <|
    IntermediateField.equivOfEq eq_adjoin_generator.symm

@[simp]
public lemma algEquiv_algebraMap (h : E ≠ ⊥) (g : K[X]) :
    algEquiv h (algebraMap K[X] K⟮X⟯ g) = aeval (generator E) g := by
  simp [algEquiv]

@[simp]
public lemma algEquiv_X (h : E ≠ ⊥) : algEquiv h (X : K⟮X⟯) = generator E := by
  simp [algEquiv]

public lemma algEquiv_apply (h : E ≠ ⊥) (u : K⟮X⟯) :
    algEquiv h u = aeval (generator E) u.num / aeval (generator E) u.denom := by
  simp [algEquiv, algEquivOfTranscendental_apply]

end
end Luroth

end RatFunc
