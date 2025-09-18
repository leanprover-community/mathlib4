/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # The positive (and negative) parts of a selfadjoint element in a C⋆-algebra

This file defines the positive and negative parts of a selfadjoint element in a C⋆-algebra via
the continuous functional calculus and develops the basic API, including the uniqueness of the
positive and negative parts.
-/

open scoped NNReal

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

namespace CStarAlgebra

noncomputable instance : PosPart A where
  posPart := cfcₙ (·⁺ : ℝ → ℝ)

noncomputable instance : NegPart A where
  negPart := cfcₙ (·⁻ : ℝ → ℝ)

end CStarAlgebra

namespace CFC

lemma posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : ℝ → ℝ) a := rfl

lemma negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : ℝ → ℝ) a := rfl

@[simp]
lemma posPart_zero : (0 : A)⁺ = 0 := by simp [posPart_def]

@[simp]
lemma negPart_zero : (0 : A)⁻ = 0 := by simp [negPart_def]

lemma posPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁺ = 0 :=
  cfcₙ_apply_of_not_predicate a ha

lemma negPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁻ = 0 :=
  cfcₙ_apply_of_not_predicate a ha

@[simp]
lemma posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

@[simp]
lemma negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total 0 x
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : a⁺ - a⁻ = a := by
  rw [posPart_def, negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id ℝ a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

section Unique

variable [T2Space A]

@[simp]
lemma posPart_neg (a : A) : (-a)⁺ = a⁻ := by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h ↦ ha (by simpa using h.neg)
    rw [posPart_def, negPart_def, cfcₙ_apply_of_not_predicate a ha,
      cfcₙ_apply_of_not_predicate _ ha']

@[simp]
lemma negPart_neg (a : A) : (-a)⁻ = a⁺ := by
  rw [← eq_comm, ← sub_eq_zero, ← posPart_neg, neg_neg, sub_self]

section SMul

variable [StarModule ℝ A]

@[simp]
lemma posPart_smul {r : ℝ≥0} {a : A} : (r • a)⁺ = r • a⁺ := by
  by_cases ha : IsSelfAdjoint a
  · simp only [CFC.posPart_def, NNReal.smul_def]
    rw [← cfcₙ_comp_smul .., ← cfcₙ_smul ..]
    refine cfcₙ_congr fun x hx ↦ ?_
    simp [_root_.posPart_def, mul_max_of_nonneg]
  · obtain (rfl | hr) := eq_or_ne r 0
    · simp
    · have := (not_iff_not.mpr <| (IsSelfAdjoint.all r).smul_iff hr.isUnit (x := a)) |>.mpr ha
      simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha,
        cfcₙ_apply_of_not_predicate _ this]

@[simp]
lemma negPart_smul {r : ℝ≥0} {a : A} : (r • a)⁻ = r • a⁻ := by
  simpa using posPart_smul (r := r) (a := -a)

lemma posPart_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) {a : A} : (r • a)⁺ = r • a⁺ :=
  posPart_smul (r := ⟨r, hr⟩)

lemma posPart_smul_of_nonpos {r : ℝ} (hr : r ≤ 0) {a : A} : (r • a)⁺ = -r • a⁻ := by
  nth_rw 1 [← neg_neg r]
  rw [neg_smul, ← smul_neg, posPart_smul_of_nonneg (neg_nonneg.mpr hr), posPart_neg]

lemma negPart_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) {a : A} : (r • a)⁻ = r • a⁻ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonpos (by simpa), neg_neg]

lemma negPart_smul_of_nonpos {r : ℝ} (hr : r ≤ 0) {a : A} : (r • a)⁻ = -r • a⁺ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonneg (by simpa)]

end SMul

end Unique

variable [PartialOrder A] [StarOrderedRing A]

@[aesop norm apply (rule_sets := [CStarAlgebra])]
lemma posPart_nonneg (a : A) :
    0 ≤ a⁺ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

@[aesop norm apply (rule_sets := [CStarAlgebra])]
lemma negPart_nonneg (a : A) :
    0 ≤ a⁻ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

lemma posPart_eq_of_eq_sub_negPart {a b : A} (hab : a = b - a⁻) (hb : 0 ≤ b := by cfc_tac) :
    a⁺ = b := by
  have ha := hab.symm ▸ hb.isSelfAdjoint.sub (negPart_nonneg a).isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hab
  simpa using hab

lemma negPart_eq_of_eq_PosPart_sub {a c : A} (hac : a = a⁺ - c) (hc : 0 ≤ c := by cfc_tac) :
    a⁻ = c := by
  have ha := hac.symm ▸ (posPart_nonneg a).isSelfAdjoint.sub hc.isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hac
  simpa using hac

lemma le_posPart {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : a ≤ a⁺ := by
  simpa [posPart_sub_negPart a] using sub_le_self a⁺ (negPart_nonneg a)

lemma neg_negPart_le {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : -a⁻ ≤ a := by
  simpa only [posPart_sub_negPart a, ← sub_eq_add_neg]
    using le_add_of_nonneg_left (a := -a⁻) (posPart_nonneg a)

variable [NonnegSpectrumClass ℝ A]

lemma posPart_eq_self (a : A) : a⁺ = a ↔ 0 ≤ a := by
  refine ⟨fun ha ↦ ha ▸ posPart_nonneg a, fun ha ↦ ?_⟩
  conv_rhs => rw [← cfcₙ_id ℝ a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx ↦ ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

lemma negPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁻ = 0 ↔ 0 ≤ a := by
  rw [← posPart_eq_self, eq_comm (b := a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

lemma negPart_eq_neg (a : A) : a⁻ = -a ↔ a ≤ 0 := by
  rw [← neg_inj, neg_neg, eq_comm]
  refine ⟨fun ha ↦ by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha ↦ ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def, ← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id ℝ a]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Unitization.quasispectrum_eq_spectrum_inr ℝ, ← neg_neg x, ← Set.mem_neg,
    spectrum.neg_eq, ← Unitization.inr_neg, ← Unitization.quasispectrum_eq_spectrum_inr ℝ] at hx
  rw [← neg_eq_iff_eq_neg, eq_comm]
  simpa using quasispectrum_nonneg_of_nonneg _ ha _ hx

lemma posPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁺ = 0 ↔ a ≤ 0 := by
  rw [← negPart_eq_neg, eq_comm (b := -a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

local notation "σₙ" => quasispectrum

open ContinuousMapZero

variable [IsTopologicalRing A] [T2Space A]

open NonUnitalContinuousFunctionalCalculus in
/-- The positive and negative parts of a selfadjoint element `a` are unique. That is, if
`a = b - c` is the difference of nonnegative elements whose product is zero, then these are
precisely `a⁺` and `a⁻`. -/
lemma posPart_negPart_unique {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
    (hb : 0 ≤ b := by cfc_tac) (hc : 0 ≤ c := by cfc_tac) :
    a⁺ = b ∧ a⁻ = c := by
  /- The key idea is to show that `cfcₙ f a = cfcₙ f b + cfcₙ f (-c)` for all real-valued `f`
  continuous on the union of the spectra of `a`, `b`, and `-c`. Then apply this to `f = (·⁺)`.
  The equality holds because both sides constitute star homomorphisms which agree on `f = id` since
  `a = b - c`. -/
  /- `a`, `b`, `-c` are selfadjoint. -/
  have hb' : IsSelfAdjoint b := .of_nonneg hb
  have hc' : IsSelfAdjoint (-c) := .neg <| .of_nonneg hc
  have ha : IsSelfAdjoint a := habc ▸ hb'.sub <| .of_nonneg hc
  /- It suffices to show `b = a⁺` since `a⁺ - a⁻ = a = b - c` -/
  rw [and_iff_left_of_imp ?of_b_eq]
  case of_b_eq =>
    rintro rfl
    exact negPart_eq_of_eq_PosPart_sub habc hc
  /- `s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)` is compact and each of these sets are subsets of `s`.
  Moreover, `0 ∈ s`. -/
  let s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)
  have hs : CompactSpace s := by
    refine isCompact_iff_compactSpace.mp <| (IsCompact.union ?_ ?_).union ?_
    all_goals exact isCompact_quasispectrum _
  obtain ⟨has, hbs, hcs⟩ : σₙ ℝ a ⊆ s ∧ σₙ ℝ b ⊆ s ∧ σₙ ℝ (-c) ⊆ s := by grind
  have : Fact (0 ∈ s) := ⟨by aesop⟩
  /- The continuous functional calculi for functions `f g : C(s, ℝ)₀` applied to `b` and `(-c)`
  are orthogonal (i.e., the product is always zero). -/
  have mul₁ (f g : C(s, ℝ)₀) :
      (cfcₙHomSuperset hb' hbs f) * (cfcₙHomSuperset hc' hcs g) = 0 := by
    refine f.nonUnitalStarAlgHom_apply_mul_eq_zero _ _ ?id ?star_id
      (cfcₙHomSuperset_continuous hb' hbs)
    case' star_id => rw [star_trivial]
    all_goals
      refine g.mul_nonUnitalStarAlgHom_apply_eq_zero _ _ ?_ ?_
        (cfcₙHomSuperset_continuous hc' hcs)
      all_goals simp only [star_trivial, cfcₙHomSuperset_id hb' hbs,
        cfcₙHomSuperset_id hc' hcs, mul_neg, hbc, neg_zero]
  have mul₂ (f g : C(s, ℝ)₀) : (cfcₙHomSuperset hc' hcs f) * (cfcₙHomSuperset hb' hbs g) = 0 := by
    simpa only [star_mul, star_zero, ← map_star, star_trivial] using congr(star $(mul₁ g f))
  /- `fun f ↦ cfcₙ f b + cfcₙ f (-c)` defines a star homomorphism `ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` which
  agrees with the star homomorphism `cfcₙ · a : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` since
  `cfcₙ id a = a = b - c = cfcₙ id b + cfcₙ id (-c)`. -/
  let ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A :=
    { (cfcₙHomSuperset hb' hbs : C(s, ℝ)₀ →ₗ[ℝ] A) + (cfcₙHomSuperset hc' hcs : C(s, ℝ)₀ →ₗ[ℝ] A)
        with
      toFun := cfcₙHomSuperset hb' hbs + cfcₙHomSuperset hc' hcs
      map_zero' := by simp [-cfcₙHomSuperset_apply]
      map_mul' := fun f g ↦ by
        simp only [Pi.add_apply, map_mul, mul_add, add_mul, mul₂, add_zero, mul₁,
          zero_add]
      map_star' := fun f ↦ by simp [← map_star] }
  have key : (cfcₙHomSuperset ha has) = ψ :=
    have : ContinuousMapZero.UniqueHom ℝ A := inferInstance
    ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id s
    (cfcₙHomSuperset ha has) ψ (cfcₙHomSuperset_continuous ha has)
    ((cfcₙHomSuperset_continuous hb' hbs).add (cfcₙHomSuperset_continuous hc' hcs))
    (by simpa [ψ, -cfcₙHomSuperset_apply, cfcₙHomSuperset_id, sub_eq_add_neg] using habc)
  /- Applying the equality of star homomorphisms to the function `(·⁺ : ℝ → ℝ)` we find that
  `b = cfcₙ id b + cfcₙ 0 (-c) = cfcₙ (·⁺) b - cfcₙ (·⁺) (-c) = cfcₙ (·⁺) a = a⁺`, where the
  second equality follows because these functions are equal on the spectra of `b` and `-c`,
  respectively, since `0 ≤ b` and `-c ≤ 0`. -/
  let f : C(s, ℝ)₀ := ⟨⟨(·⁺), by fun_prop⟩, by simp; exact le_rfl⟩
  replace key := congr($key f)
  simp only [cfcₙHomSuperset_apply, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk, ψ,
    Pi.add_apply, cfcₙHom_eq_cfcₙ_extend (·⁺)] at key
  symm
  calc
    b = cfcₙ (id : ℝ → ℝ) b + cfcₙ (0 : ℝ → ℝ) (-c) := by simp [cfcₙ_id ℝ b]
    _ = _ := by
      congr! 1
      all_goals
        refine cfcₙ_congr fun x hx ↦ Eq.symm ?_
        lift x to σₙ ℝ _ using hx
        simp only [Subtype.val_injective.extend_apply, comp_apply, coe_mk,
          ContinuousMap.coe_mk, Subtype.map_coe, id_eq, _root_.posPart_eq_self, f, Pi.zero_apply,
          posPart_eq_zero]
      · exact quasispectrum_nonneg_of_nonneg b hb x.val x.property
      · obtain ⟨x, hx⟩ := x
        simp only [← neg_nonneg]
        rw [Unitization.quasispectrum_eq_spectrum_inr ℝ (-c), Unitization.inr_neg,
          ← spectrum.neg_eq, Set.mem_neg, ← Unitization.quasispectrum_eq_spectrum_inr ℝ c]
          at hx
        exact quasispectrum_nonneg_of_nonneg c hc _ hx
    _ = _ := key.symm
    _ = a⁺ := by
      refine cfcₙ_congr fun x hx ↦ ?_
      lift x to σₙ ℝ a using hx
      simp [f]

end CFC

end NonUnital

section Unital

namespace CFC

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [T2Space A]

@[simp]
lemma posPart_one : (1 : A)⁺ = 1 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
lemma negPart_one : (1 : A)⁻ = 0 := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
lemma posPart_algebraMap (r : ℝ) : (algebraMap ℝ A r)⁺ = algebraMap ℝ A r⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
lemma negPart_algebraMap (r : ℝ) : (algebraMap ℝ A r)⁻ = algebraMap ℝ A r⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simp

open NNReal in
@[simp]
lemma posPart_algebraMap_nnreal (r : ℝ≥0) : (algebraMap ℝ≥0 A r)⁺ = algebraMap ℝ≥0 A r := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc, IsScalarTower.algebraMap_apply ℝ≥0 ℝ A]
  simp

open NNReal in
@[simp]
lemma posPart_natCast (n : ℕ) : (n : A)⁺ = n := by
  rw [← map_natCast (algebraMap ℝ≥0 A), posPart_algebraMap_nnreal]

end CFC

end Unital

section SpanNonneg

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
variable [StarRing A] [TopologicalSpace A] [StarModule ℂ A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

open Submodule Complex
open scoped ComplexStarModule

lemma CStarAlgebra.linear_combination_nonneg (x : A) :
    ((ℜ x : A)⁺ - (ℜ x : A)⁻) + (I • (ℑ x : A)⁺ - I • (ℑ x : A)⁻) = x := by
  rw [CFC.posPart_sub_negPart _ (ℜ x).2, ← smul_sub, CFC.posPart_sub_negPart _ (ℑ x).2,
    realPart_add_I_smul_imaginaryPart x]

variable [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-algebra is spanned by its nonnegative elements. -/
lemma CStarAlgebra.span_nonneg : Submodule.span ℂ {a : A | 0 ≤ a} = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← CStarAlgebra.linear_combination_nonneg x]
  apply_rules [sub_mem, Submodule.smul_mem, add_mem]
  all_goals
    refine subset_span ?_
    first | apply CFC.negPart_nonneg | apply CFC.posPart_nonneg

end SpanNonneg
