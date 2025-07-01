/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Star

/-!
# Definition of BoundedContinuousFunction.char

Definition and basic properties of `BoundedContinuousFunction.char he hL w := fun v ↦ e (L v w)`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear
map.

In the special case `e = Circle.exp`, this is used to define the characteristic function of a
measure.

## Main definitions

- `char he hL w : V →ᵇ ℂ`: Bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`, where
  `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear map.
- `charPoly he hL : W → ℂ`: The `StarSubalgebra ℂ (V →ᵇ ℂ)` consisting of `ℂ`-linear combinations of
  `char he hL w`, where `w : W`.

## Main statements

- `ext_of_char_eq`: If `e` and `L` are non-trivial, then `char he hL w, w : W` separates
  points in `V`.
- `star_mem_range_charAlgHom`: The family of `ℂ`-linear combinations of `char he hL w, w : W`, is
  closed under `star`.
- `separatesPoints_charPoly`: The family `charPoly he hL w, w : W` separates points in `V`.

-/

open Filter BoundedContinuousFunction Complex

namespace BoundedContinuousFunction

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {he : Continuous e} {hL : Continuous fun p : V × W ↦ L p.1 p.2}

/-- The bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`. -/
noncomputable def char (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) :
    V →ᵇ ℂ where
  toFun := fun v ↦ e (L v w)
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y ↦ ?_⟩
    calc dist _ _
      ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]
lemma char_apply (w : W) (v : V) :
    char he hL w v = e (L v w) := rfl

@[simp]
lemma char_zero_eq_one : char he hL 0 = 1 := by ext; simp

lemma char_add_eq_mul (x y : W) :
    char he hL (x + y) = char he hL x * char he hL y := by
  ext
  simp [e.map_add_eq_mul]

lemma char_neg (w : W) :
    char he hL (-w) = star (char he hL w) := by ext; simp

/-- If `e` and `L` are non-trivial, then `char he hL w, w : W` separates points in `V`. -/
theorem ext_of_char_eq (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) {v v' : V}
    (h : ∀ w, char he hL w v = char he hL w v') :
    v = v' := by
  contrapose! h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne h))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, char_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _), div_eq_inv_mul, ← Metric.unitSphere.coe_inv,
    ← e.map_neg_eq_inv, ← Submonoid.coe_mul, ← e.map_add_eq_mul, OneMemClass.coe_eq_one]
  calc e (- L v' ((a / (L v w - L v' w)) • w) + L v ((a / (L v w - L v' w)) • w))
  _ = e (- (a / (L v w - L v' w)) • L v' w + (a / (L v w - L v' w)) • L v w) := by
    congr
    · rw [neg_smul, ← LinearMap.map_smul (L v')]
    · rw [← LinearMap.map_smul (L v)]
  _ = e ((a / (L (v - v') w)) • (L (v - v') w)) := by
    simp only [map_sub, LinearMap.sub_apply]
    congr
    module
  _ = e a := by
    congr
    exact div_mul_cancel₀ a hw
  _ ≠ 1 := ha

/-- Monoid homomorphism mapping `w` to `fun v ↦ e (L v w)`. -/
noncomputable def charMonoidHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    Multiplicative W →* (V →ᵇ ℂ) where
  toFun w := char he hL w
  map_one' := char_zero_eq_one
  map_mul' := char_add_eq_mul (he := he) (hL := hL)

@[simp]
lemma charMonoidHom_apply (w : Multiplicative W) (v : V) :
    charMonoidHom he hL w v = e (L v w) := by simp [charMonoidHom]

/-- Algebra homomorphism mapping `w` to `fun v ↦ e (L v w)`. -/
noncomputable
def charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    AddMonoidAlgebra ℂ W →ₐ[ℂ] (V →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℂ W (V →ᵇ ℂ) (charMonoidHom he hL)

@[simp]
lemma charAlgHom_apply (w : AddMonoidAlgebra ℂ W) (v : V) :
    charAlgHom he hL w v = ∑ a ∈ w.support, w a * (e (L v a) : ℂ) := by
  simp only [charAlgHom, AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum_of_support_subset w subset_rfl]
  · simp only [coe_sum, coe_smul, charMonoidHom_apply, smul_eq_mul, Finset.sum_apply]
    rfl
  · simp

/-- The family of `ℂ`-linear combinations of `char he hL w, w : W`, is closed under `star`. -/
lemma star_mem_range_charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {x : V →ᵇ ℂ} (hx : x ∈ (charAlgHom he hL).range) :
    star x ∈ (charAlgHom he hL).range := by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := Finsupp.mapRange star (star_zero _) y
  let f : W ↪ W := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩
  refine ⟨z.embDomain f, ?_⟩
  ext1 u
  simp only [charAlgHom_apply, Finsupp.support_embDomain, Finset.sum_map,
    Finsupp.embDomain_apply, star_apply, star_sum, star_mul', Circle.star_addChar]
  rw [Finsupp.support_mapRange_of_injective (star_zero _) y star_injective]
  simp [z, f]

/-- The star-subalgebra of polynomials. -/
noncomputable
def charPoly (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    StarSubalgebra ℂ (V →ᵇ ℂ) where
  toSubalgebra := (charAlgHom he hL).range
  star_mem' hx := star_mem_range_charAlgHom he hL hx

lemma mem_charPoly (f : V →ᵇ ℂ) :
    f ∈ charPoly he hL
      ↔ ∃ w : AddMonoidAlgebra ℂ W, f = fun x ↦ ∑ a ∈ w.support, w a * (e (L x a) : ℂ) := by
  change f ∈ (charAlgHom he hL).range ↔ _
  simp [BoundedContinuousFunction.ext_iff, funext_iff, eq_comm]

lemma char_mem_charPoly (w : W) : char he hL w ∈ charPoly he hL := by
  rw [mem_charPoly]
  refine ⟨AddMonoidAlgebra.single w 1, ?_⟩
  ext v
  simp only [char_apply, AddMonoidAlgebra.single]
  rw [Finset.sum_eq_single w]
  · simp only [Finsupp.single_eq_same, one_mul]
  · simp [Finsupp.single_apply_ne_zero]
  · simp

/-- The family `charPoly he hL w, w : W` separates points in `V`. -/
lemma separatesPoints_charPoly (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) :
    ((charPoly he hL).map (toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ : ∃ w, char he hL w v ≠ char he hL w v' := by
    contrapose! hvv'
    exact ext_of_char_eq he he' hL hL' hvv'
  use char he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨char he hL w, char_mem_charPoly w, rfl⟩, hw⟩

end BoundedContinuousFunction
