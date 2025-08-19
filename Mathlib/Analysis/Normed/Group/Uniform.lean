/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Normed groups are uniform groups

This file proves lipschitzness of normed group operations and shows that normed groups are uniform
groups.
-/

variable {𝓕 E F : Type*}

open Filter Function Metric Bornology
open scoped ENNReal NNReal Uniformity Pointwise Topology

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F] {s : Set E} {a b : E} {r : ℝ}

@[to_additive]
instance NormedGroup.to_isIsometricSMul_right : IsIsometricSMul Eᵐᵒᵖ E :=
  ⟨fun a ↦ Isometry.of_dist_eq fun b c ↦ by simp [dist_eq_norm_div]⟩

@[to_additive]
theorem Isometry.norm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖ = ‖x‖ := by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]

@[to_additive (attr := simp) norm_map]
theorem norm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖ = ‖x‖ :=
  (IsometryClass.isometry f).norm_map_of_map_one (map_one f) x

@[to_additive (attr := simp) nnnorm_map]
theorem nnnorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map' f x

@[to_additive (attr := simp)]
theorem dist_mul_self_right (a b : E) : dist b (a * b) = ‖a‖ := by
  rw [← dist_one_left, ← dist_mul_right 1 a b, one_mul]

@[to_additive (attr := simp)]
theorem dist_mul_self_left (a b : E) : dist (a * b) b = ‖a‖ := by
  rw [dist_comm, dist_mul_self_right]

@[to_additive (attr := simp)]
theorem dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b) := by
  rw [← dist_mul_right _ _ b, div_mul_cancel]

@[to_additive (attr := simp)]
theorem dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b := by
  rw [← dist_mul_right _ _ c, div_mul_cancel]

open Finset

variable [FunLike 𝓕 E F]

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/NormedSpace/OperatorNorm.lean`. -/
@[to_additive /-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/NormedSpace/OperatorNorm.lean`. -/]
theorem MonoidHomClass.lipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : LipschitzWith (Real.toNNReal C) f :=
  LipschitzWith.of_dist_le' fun x y ↦ by simpa only [dist_eq_norm_div, map_div] using h (x / y)

@[to_additive]
theorem lipschitzOnWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzOnWith C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le

attribute [to_additive] LipschitzOnWith.norm_div_le

@[to_additive]
theorem LipschitzOnWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzOnWith C f s)
    (ha : a ∈ s) (hb : b ∈ s) (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le ha hb).trans <| by gcongr

@[to_additive]
theorem lipschitzWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzWith C f ↔ ∀ x y, ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le

attribute [to_additive] LipschitzWith.norm_div_le

@[to_additive]
theorem LipschitzWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzWith C f)
    (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le _ _).trans <| by gcongr

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/
@[to_additive /-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/]
theorem MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : Continuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).continuous

@[to_additive]
theorem MonoidHomClass.uniformContinuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : UniformContinuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous

@[to_additive]
theorem MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    Isometry f ↔ ∀ x, ‖f x‖ = ‖x‖ := by
  simp only [isometry_iff_dist_eq, dist_eq_norm_div, ← map_div]
  refine ⟨fun h x ↦ ?_, fun h x y ↦ h _⟩
  simpa using h x 1

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm

attribute [to_additive] MonoidHomClass.isometry_of_norm

section NNNorm

@[to_additive]
theorem MonoidHomClass.lipschitz_of_bound_nnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ≥0)
    (h : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) : LipschitzWith C f :=
  @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h

@[to_additive]
theorem MonoidHomClass.antilipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y ↦ by
    simpa only [dist_eq_norm_div, map_div] using h (x / y)

@[to_additive LipschitzWith.norm_le_mul]
theorem LipschitzWith.norm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖ ≤ K * ‖x‖ := by simpa only [dist_one_right, hf] using h.dist_le_mul x 1

@[to_additive LipschitzWith.nnorm_le_mul]
theorem LipschitzWith.nnorm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖₊ ≤ K * ‖x‖₊ :=
  h.norm_le_mul' hf x

@[to_additive AntilipschitzWith.le_mul_norm]
theorem AntilipschitzWith.le_mul_norm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖ ≤ K * ‖f x‖ := by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1

@[to_additive AntilipschitzWith.le_mul_nnnorm]
theorem AntilipschitzWith.le_mul_nnnorm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖₊ ≤ K * ‖f x‖₊ :=
  h.le_mul_norm' hf x

@[to_additive]
theorem OneHomClass.bound_of_antilipschitz [OneHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : AntilipschitzWith K f) (x) : ‖x‖ ≤ K * ‖f x‖ :=
  h.le_mul_nnnorm' (map_one f) x

@[to_additive]
theorem Isometry.nnnorm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
  Subtype.ext <| hi.norm_map_of_map_one h₁ x

end NNNorm

@[to_additive lipschitzWith_one_norm]
theorem lipschitzWith_one_norm' : LipschitzWith 1 (norm : E → ℝ) := by
  simpa using LipschitzWith.dist_right (1 : E)

@[to_additive lipschitzWith_one_nnnorm]
theorem lipschitzWith_one_nnnorm' : LipschitzWith 1 (NNNorm.nnnorm : E → ℝ≥0) :=
  lipschitzWith_one_norm'

@[to_additive uniformContinuous_norm]
theorem uniformContinuous_norm' : UniformContinuous (norm : E → ℝ) :=
  lipschitzWith_one_norm'.uniformContinuous

@[to_additive uniformContinuous_nnnorm]
theorem uniformContinuous_nnnorm' : UniformContinuous fun a : E ↦ ‖a‖₊ :=
  uniformContinuous_norm'.subtype_mk _

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a₁ a₂ b₁ b₂ : E} {r₁ r₂ : ℝ}

@[to_additive]
instance NormedGroup.to_isIsometricSMul_left : IsIsometricSMul E E :=
  ⟨fun a ↦ Isometry.of_dist_eq fun b c ↦ by simp [dist_eq_norm_div]⟩

@[to_additive (attr := simp)]
theorem dist_self_mul_right (a b : E) : dist a (a * b) = ‖b‖ := by
  rw [← dist_one_left, ← dist_mul_left a 1 b, mul_one]

@[to_additive (attr := simp)]
theorem dist_self_mul_left (a b : E) : dist (a * b) a = ‖b‖ := by
  rw [dist_comm, dist_self_mul_right]

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this
theorem dist_self_div_right (a b : E) : dist a (a / b) = ‖b‖ := by
  rw [div_eq_mul_inv, dist_self_mul_right, norm_inv']

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this
theorem dist_self_div_left (a b : E) : dist (a / b) a = ‖b‖ := by
  rw [dist_comm, dist_self_div_right]

@[to_additive]
theorem dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive]
theorem dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ * a₂) (b₁ * b₂) ≤ r₁ + r₂ :=
  (dist_mul_mul_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂

@[to_additive]
theorem dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive]
theorem dist_div_div_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ / a₂) (b₁ / b₂) ≤ r₁ + r₂ :=
  (dist_div_div_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂

@[to_additive]
theorem abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) :
    |dist a₁ b₁ - dist a₂ b₂| ≤ dist (a₁ * a₂) (b₁ * b₂) := by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

open Finset

@[to_additive]
theorem nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    nndist (a₁ * a₂) (b₁ * b₂) ≤ nndist a₁ b₁ + nndist a₂ b₂ :=
  NNReal.coe_le_coe.1 <| dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]
theorem edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    edist (a₁ * a₂) (b₁ * b₂) ≤ edist a₁ b₁ + edist a₂ b₂ := by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le

section PseudoEMetricSpace
variable {α E : Type*} [SeminormedCommGroup E] [PseudoEMetricSpace α] {K Kf Kg : ℝ≥0}
  {f g : α → E} {s : Set α}

@[to_additive (attr := simp)]
lemma lipschitzWith_inv_iff : LipschitzWith K f⁻¹ ↔ LipschitzWith K f := by simp [LipschitzWith]

@[to_additive (attr := simp)]
lemma antilipschitzWith_inv_iff : AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K f := by
  simp [AntilipschitzWith]

@[to_additive (attr := simp)]
lemma lipschitzOnWith_inv_iff : LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s := by
  simp [LipschitzOnWith]

@[to_additive (attr := simp)]
lemma locallyLipschitz_inv_iff : LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f := by
  simp [LocallyLipschitz]

@[to_additive (attr := simp)]
lemma locallyLipschitzOn_inv_iff : LocallyLipschitzOn s f⁻¹ ↔ LocallyLipschitzOn s f := by
  simp [LocallyLipschitzOn]

@[to_additive] alias ⟨LipschitzWith.of_inv, LipschitzWith.inv⟩ := lipschitzWith_inv_iff
@[to_additive] alias ⟨AntilipschitzWith.of_inv, AntilipschitzWith.inv⟩ := antilipschitzWith_inv_iff
@[to_additive] alias ⟨LipschitzOnWith.of_inv, LipschitzOnWith.inv⟩ := lipschitzOnWith_inv_iff
@[to_additive] alias ⟨LocallyLipschitz.of_inv, LocallyLipschitz.inv⟩ := locallyLipschitz_inv_iff
@[to_additive]
alias ⟨LocallyLipschitzOn.of_inv, LocallyLipschitzOn.inv⟩ := locallyLipschitzOn_inv_iff

@[to_additive]
lemma LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (fun x ↦ f x * g x) s := fun x hx y hy ↦
  calc
    edist (f x * g x) (f y * g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf hx hy) (hg hx hy)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[to_additive]
lemma LipschitzWith.mul (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x ↦ f x * g x := by
  simpa [← lipschitzOnWith_univ] using hf.lipschitzOnWith.mul hg.lipschitzOnWith

@[to_additive]
lemma LocallyLipschitzOn.mul (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s fun x ↦ f x * g x := fun x hx ↦ by
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg hx
  exact ⟨Kf + Kg, t ∩ u, inter_mem ht hu,
    (hKf.mono Set.inter_subset_left).mul (hKg.mono Set.inter_subset_right)⟩

@[to_additive]
lemma LocallyLipschitz.mul (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x ↦ f x * g x := by
  simpa [← locallyLipschitzOn_univ] using hf.locallyLipschitzOn.mul hg.locallyLipschitzOn

@[to_additive]
lemma LipschitzOnWith.div (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (fun x ↦ f x / g x) s := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

@[to_additive]
theorem LipschitzWith.div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x ↦ f x / g x := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

@[to_additive]
lemma LocallyLipschitzOn.div (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s fun x ↦ f x / g x := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

@[to_additive]
lemma LocallyLipschitz.div (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x ↦ f x / g x := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

namespace AntilipschitzWith

@[to_additive]
theorem mul_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x ↦ f x * g x := by
  letI : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  rw [NNReal.coe_inv, ← _root_.div_eq_inv_mul]
  rw [le_div_iff₀ (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm, NNReal.coe_sub hK.le, sub_mul]
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ ≤ _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)

@[to_additive]
theorem mul_div_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
    (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [Pi.div_apply, mul_div_cancel] using hf.mul_lipschitzWith hg hK

@[to_additive le_mul_norm_sub]
theorem le_mul_norm_div {f : E → F} (hf : AntilipschitzWith K f) (x y : E) :
    ‖x / y‖ ≤ K * ‖f x / f y‖ := by simp [← dist_eq_norm_div, hf.le_mul_dist x y]

end AntilipschitzWith
end PseudoEMetricSpace

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.to_lipschitzMul : LipschitzMul E :=
  ⟨⟨1 + 1, LipschitzWith.prod_fst.mul LipschitzWith.prod_snd⟩⟩

-- See note [lower instance priority]
/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[to_additive /-- A seminormed group is a uniform additive group, i.e., addition and subtraction are
uniformly continuous. -/]
instance (priority := 100) SeminormedCommGroup.to_isUniformGroup : IsUniformGroup E :=
  ⟨(LipschitzWith.prod_fst.div LipschitzWith.prod_snd).uniformContinuous⟩

-- short-circuit type class inference
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toIsTopologicalGroup : IsTopologicalGroup E :=
  inferInstance

/-! ### SeparationQuotient -/

namespace SeparationQuotient

@[to_additive instNorm]
instance instMulNorm : Norm (SeparationQuotient E) where
  norm := lift Norm.norm fun _ _ h ↦ h.norm_eq_norm'

set_option linter.docPrime false in
@[to_additive (attr := simp) norm_mk]
theorem norm_mk' (p : E) : ‖mk p‖ = ‖p‖ := rfl

@[to_additive]
instance : NormedCommGroup (SeparationQuotient E) where
  __ : CommGroup (SeparationQuotient E) := instCommGroup
  dist_eq := Quotient.ind₂ dist_eq_norm_div

@[to_additive]
theorem mk_eq_one_iff {p : E} : mk p = 1 ↔ ‖p‖ = 0 := by
  rw [← norm_mk', norm_eq_zero']

set_option linter.docPrime false in
@[to_additive (attr := simp) nnnorm_mk]
theorem nnnorm_mk' (p : E) : ‖mk p‖₊ = ‖p‖₊ := rfl

end SeparationQuotient

@[to_additive]
theorem cauchySeq_prod_of_eventually_eq {u v : ℕ → E} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
    (hv : CauchySeq fun n ↦ ∏ k ∈ range (n + 1), v k) :
    CauchySeq fun n ↦ ∏ k ∈ range (n + 1), u k := by
  let d : ℕ → E := fun n ↦ ∏ k ∈ range (n + 1), u k / v k
  rw [show (fun n ↦ ∏ k ∈ range (n + 1), u k) = d * fun n ↦ ∏ k ∈ range (n + 1), v k
      by ext n; simp [d]]
  suffices ∀ n ≥ N, d n = d N from (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod _ (add_le_add_right hn 1)]
  intro m hm
  simp [huv m (le_of_lt hm)]

@[to_additive CauchySeq.norm_bddAbove]
lemma CauchySeq.mul_norm_bddAbove {G : Type*} [SeminormedGroup G] {u : ℕ → G}
    (hu : CauchySeq u) : BddAbove (Set.range (fun n ↦ ‖u n‖)) := by
  obtain ⟨C, -, hC⟩ := cauchySeq_bdd hu
  simp_rw [SeminormedGroup.dist_eq] at hC
  have : ∀ n, ‖u n‖ ≤ C + ‖u 0‖ := by
    intro n
    rw [add_comm]
    refine (norm_le_norm_add_norm_div' (u n) (u 0)).trans ?_
    simp [(hC _ _).le]
  rw [bddAbove_def]
  exact ⟨C + ‖u 0‖, by simpa using this⟩

end SeminormedCommGroup
