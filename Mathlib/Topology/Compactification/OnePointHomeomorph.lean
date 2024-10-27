/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Topology.Compactification.OnePointEquiv
import Mathlib.Topology.Compactification.OnePointSlope
import Mathlib.Topology.Compactification.OnePointRealLemmas

/-!
# Homeomorphism between one-point compactification and projective space


We prove that slope, suitably defined, is a homeomorphism from ℙ ℝ (Fin 2 → ℝ) to OnePoint ℝ.
In particular with our notion of slope, 1 ÷ 0 = ∞.

## Main results

* `onepointhomeo`: The desired homeomorphism.

## Tags

homeomorphism, projective
-/

open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization


open Classical

/-- The inverse of `r` is `1 / r`, with `1 / 0 = ∞`.-/
noncomputable def OnePoint_inv (r : ℝ) : OnePoint ℝ := ite (r ≠ 0) (some ((1:ℝ)/r)) ∞

/-- Ordinary division is continuous. -/
lemma cont_inv_lift_ (a x:ℝ) (h : x ≠ 0) :
    ContinuousAt (fun x : ℝ ↦ ( (a / x) : OnePoint ℝ)) x := by
  apply ContinuousAt.comp'
  · exact Continuous.continuousAt OnePoint.continuous_coe
  · apply ContinuousAt.div₀
    · exact continuousAt_const
    repeat tauto

/-- OnePoint_div is continuous. -/
lemma cont_nonzero_ (a x:ℝ) (h: x ≠ 0) : ContinuousAt (OnePoint_div a) x := by
  rw [continuousAt_congr]
  · show ContinuousAt (fun x : ℝ ↦ ( (a / x) : OnePoint ℝ)) x
    apply cont_inv_lift_; tauto

  · unfold Filter.EventuallyEq OnePoint_div;simp;
    rw [eventually_nhds_iff]
    by_cases H : 0 < x
    · use Set.Ioo (x/2) (2*x)
      constructor
      · intro y hy
        simp at hy
        have : y ≠ 0 := by
          linarith
        simp_all
      · constructor
        · exact isOpen_Ioo
        · refine Set.mem_Ioo.mpr ?h.right.right.a;
          constructor
          · simp_all only [half_lt_self_iff]
          · simp_all only [lt_mul_iff_one_lt_left, Nat.one_lt_ofNat]
    use Set.Ioo (2*x) (x/2)
    constructor
    · intro y hy
      simp at hy
      have : y ≠ 0 := by linarith
      simp_all

    · simp_all
      have : x < 0 := lt_of_le_of_ne H h
      constructor
      · exact isOpen_Ioo
      · constructor
        · linarith
        · linarith

/-- Auxiliary fact. -/
lemma in_onepoint_set
    {t : Set (OnePoint ℝ)} {a₀ a₁ : ℝ}
    (ha : ∀ (b : ℝ), b ≤ -(max |a₀| |a₁|) ∨ (max |a₀| |a₁|) ≤ b → some b ∈ t)
    (hap : max |a₀| |a₁| > 0) (h : ∞ ∈ t)
    (x : ℝ) (hx : |x| ≤ (max |a₀| |a₁|)⁻¹) :
    (if x = 0 then ∞ else some x⁻¹) ∈ t := by
  split_ifs
  · simp_all
  · apply ha; apply abs_le_inv; repeat tauto

/-- Auxiliary fact. -/
lemma suffice
    (t : Set (OnePoint ℝ))
    (x : ℝ)
    (h : ∃ ε > 0, ∀ (y : ℝ), |x - y| ≤ ε → (if y = 0 then ∞ else ↑y⁻¹) ∈ t) :
    ∃ V ∈ uniformity ℝ, {y | (x, y) ∈ V} ⊆ {r | (if r = 0 then ∞ else some r⁻¹) ∈ t} := by
  obtain ⟨ε,hε⟩ := h
  use {(x,y) | dist x y ≤ ε}
  rw [Metric.mem_uniformity_dist]
  constructor
  · use ε
    constructor
    · tauto
    · intros;simp;linarith
  · apply hε.2

/-- Function underlying homeomorphism. -/
noncomputable def div_slope (p : ℙ ℝ (Fin 2 → ℝ)) : OnePoint ℝ :=
  Quotient.lift
    (fun u : { v : Fin 2 → ℝ // v ≠ 0} ↦
      OnePoint_div (u.1 0) (u.1 1)) div_slope_well_defined p

/-- Division is injective. -/
lemma div_slope_injective : Function.Injective div_slope :=
  Quotient.ind (fun a ↦ Quotient.ind (field_div_slope_inj_lifted a))

/-- Division is continnuous. -/
lemma continuous_slope_nonzero_case {x : { v : Fin 2 → ℝ // v ≠ 0 }} (hx : ¬x.1 1 = 0) :
    ContinuousAt (fun u ↦ u.1 0 ÷ u.1 1) x := by
  have : (fun u ↦ u.1 0 ÷ u.1 1) =ᶠ[nhds x] fun v ↦ OnePoint.some (v.1 0 / v.1 1) := by
      unfold Filter.EventuallyEq OnePoint_div
      simp only [ne_eq, Fin.isValue, ite_not, ite_eq_right_iff,
        OnePoint.infty_ne_coe, imp_false];
      exact eventually_nhds_iff.mpr (open_nonzero hx)
  rw [continuousAt_congr this]

  apply ContinuousAt.comp'
  · exact Continuous.continuousAt OnePoint.continuous_coe
  refine ContinuousAt.div₀ ?_ ?_ hx

  · exact ContinuousAt.comp (continuousAt_apply 0 x.1) continuousAt_subtype_val
  · exact ContinuousAt.comp (continuousAt_apply 1 x.1) continuousAt_subtype_val

/-- Auxiliary nhds lemma.  -/
lemma slope_open_nonzero
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₁ : IsOpen (OnePoint.some ⁻¹' t))
    {a : { v : Fin 2 → ℝ // ¬v = 0 }}
    (ha : (if a.1 1 = 0 then ∞ else some (a.1 0 / a.1 1)) ∈ t)
    (H : ¬a.1 1 = 0) :
    (fun u : { v : Fin 2 → ℝ // v ≠ 0} ↦
    if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t ∈ nhds a := by
  rw [if_neg H] at ha
  have Q := continuous_slope_nonzero_case H
  rw [continuousAt_def] at Q
  unfold OnePoint_div at Q
  simp only [ne_eq, Fin.isValue, ite_not] at Q
  apply Q
  rw [if_neg H]
  refine IsOpen.mem_nhds ?_ ha
  refine OnePoint.isOpen_def.mpr ?_
  tauto

/-- Auxiliary uniformity lemma.  -/
lemma slope_uniform_of_compact_pos
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin 2 → ℝ // v ≠ 0 }}
    (H : a.1 1 = 0)
    (hl : a.1 0 > 0) : ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t :=  by
  have W := IsCompact.isBounded (ht₀)
  rw [Bornology.isBounded_def] at W
  simp at W
  obtain ⟨⟨a₀,ha₀⟩,⟨a₁,ha₁⟩⟩ := W

  let amax := max |a₀| |a₁|
  have hamax : ∀ b : ℝ, b ≤ -amax ∨ amax ≤ b → some b ∈ t := by
    apply symmetrize;exact ha₀;exact ha₁
  let Q := dist_cone_pos H hl (show amax ≥ 0 by positivity)
  obtain ⟨δ,hδ⟩ := Q
  use {(u,v) | dist u.1 v.1 < δ}
  constructor
  · refine Metric.dist_mem_uniformity ?h.left.ε0
    tauto
  · intro x h_x
    simp at h_x
    have hx : dist a x < δ := h_x
    clear h_x
    simp only [ne_eq, Fin.isValue, Set.mem_preimage]
    by_cases hz : x.1 1 = 0
    · rw [hz];simp;tauto
    · rw [if_neg hz]
      apply hamax
      by_cases hpos : x.1 1 > 0
      · right
        have : dist a x = dist a.1 x.1 := rfl
        have hδ' := hδ.2 x.1 (by rw [dist_comm];linarith)
        tauto
      · left
        have h₁: x.1 1 < 0 := lt_of_le_of_ne (le_of_not_lt hpos) hz
        rw [dist_comm] at hx
        have : dist x.1 a.1 < δ := hx
        have h₀: dist x.1 a.1 ≤ δ := by linarith
        exact (hδ.2 x h₀).1 h₁

/-- Auxiliary uniformity lemma.  -/
lemma slope_uniform_of_compact_neg {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ) (ht₂ : ∞ ∈ t)
    {a : { v : Fin 2 → ℝ // v ≠ 0 }} (H : a.1 1 = 0) (hl : a.1 0 < 0) :
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t :=  by
  have W := IsCompact.isBounded (ht₀)
  rw [Bornology.isBounded_def] at W
  simp at W
  obtain ⟨⟨a₀,ha₀⟩,⟨a₁,ha₁⟩⟩ := W

  let amax := max |a₀| |a₁|
  have hamax : ∀ b : ℝ, b ≤ -amax ∨ amax ≤ b → some b ∈ t := by
    apply symmetrize;exact ha₀;exact ha₁
  let Q := dist_cone_neg H hl (show amax ≥ 0 by positivity)
  obtain ⟨δ,hδ⟩ := Q
  use {(u,v) | dist u v < δ}
  constructor
  · exact Metric.dist_mem_uniformity hδ.1
  · intro x h_x
    have hx : dist a x < δ := h_x
    clear h_x
    simp only [ne_eq, Fin.isValue, Set.mem_preimage]
    by_cases X : x.1 1 = 0
    · rw [X];simp;tauto
    · rw [if_neg X];
      apply hamax
      by_cases hpos : x.1 1 > 0
      · left
        have : dist a x = dist a.1 x.1 := rfl
        have hδ' := hδ.2 x.1 (by rw [dist_comm];linarith)
        tauto
      · right
        have hneg: x.1 1 < 0 := lt_of_le_of_ne (le_of_not_lt hpos) X
        rw [dist_comm] at hx
        have : dist x.1 a.1 < δ := hx
        have h₀: dist x.1 a.1 ≤ δ := by linarith
        exact (hδ.2 x h₀).2 hneg

/-- Auxiliary uniformity lemma.  -/
lemma slope_uniform_of_compact
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin 2 → ℝ // v ≠ 0 }}
    (H : a.1 1 = 0) :
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t := by
  cases (pos_or_neg H) with
  |inl hl => exact slope_uniform_of_compact_pos ht₀ ht₂ H hl
  |inr hr => exact slope_uniform_of_compact_neg ht₀ ht₂ H hr

/-- Auxiliary openness lemma.  -/
lemma slope_open
    {t : Set (OnePoint ℝ)}
    (h_t : IsOpen t ∧ ∞ ∈ t) :
    IsOpen ((fun u : { v : Fin 2 → ℝ // v ≠ 0 }
    ↦ if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t) := by
  rw [OnePoint.isOpen_def] at h_t
  have ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ := by tauto
  have ht₁ : IsOpen (OnePoint.some ⁻¹' t) := by tauto
  have ht₂ : ∞ ∈ t := by tauto
  clear h_t
  rw [isOpen_iff_nhds]
  intro a ha
  simp_all;
  by_cases H : a.1 1 = 0
  · have Q := slope_uniform_of_compact ht₀ ht₂ H
    obtain ⟨V,hV⟩ := Q
    rw [nhds_eq_comap_uniformity]
    simp;use V;simp_all;tauto
  · exact slope_open_nonzero ht₀ ht₁ ha H

/-- Auxiliary continuity lemma.  -/
lemma continuous_slope_zero_case (x : { v : Fin 2 → ℝ // v ≠ 0 }) (H₁ : x.1 1 = 0) :
    ContinuousAt (fun u ↦ u.1 0 ÷ u.1 1) x := by
  unfold OnePoint_div
  rw [continuousAt_def]
  intro A hA
  rw [mem_nhds_iff] at *
  obtain ⟨t,ht⟩ := hA
  use (fun u ↦ if u.1 1 = 0 then ∞ else Option.some (u.1 0 / u.1 1)) ⁻¹' t
  constructor
  · intro a ha
    simp only [ne_eq, Fin.isValue, Set.mem_preimage] at ha
    simp only [ne_eq, Fin.isValue, ite_not, Set.mem_preimage]
    split_ifs with h₀
    · simp_all only [ne_eq, not_true_eq_false, div_zero, ite_false, ite_true]
      tauto
    · rw [if_neg h₀] at *; tauto
  · simp_all only [ne_eq, not_true_eq_false, div_zero, ite_false, Set.mem_preimage, ite_true,
    and_true]
    apply slope_open
    tauto

/-- Auxiliary continuity lemma.  -/
theorem div_slope_continuous_unlifted :
    Continuous fun u : { v : Fin 2 → ℝ // v ≠ 0 } ↦ (u.1 0) ÷ (u.1 1) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases H₁ : x.1 1 = 0
  · apply continuous_slope_zero_case;tauto
  · apply continuous_slope_nonzero_case;tauto

/-- Topology on projectivization. -/
instance {n : ℕ}: TopologicalSpace (ℙ ℝ (Fin n → ℝ)) := instTopologicalSpaceQuot

/-- div_slope is continuous. -/
theorem div_slope_continuous : Continuous div_slope := by
  apply continuous_quot_lift
  apply div_slope_continuous_unlifted

/-- List from unit circle to projectivization. -/
def lift_unit_circle {n:ℕ}  : {v : Fin n → ℝ // dist v 0 = 1} → ℙ ℝ (Fin n → ℝ) := by
  intro v
  exact mk' ℝ ⟨v.1,by
    intro hc;
    have : dist v.1 0 = 1 := v.2
    rw [hc] at this;simp_all
  ⟩

/-- List from unit circle to projectivization is surjective. -/
lemma surjective_lift_unit_circle {n:ℕ} :
    Function.Surjective (@lift_unit_circle n) :=
  Quotient.ind (fun x ↦ by
    have := x.2
    have : ‖x.1‖ ≠ 0 := by simp_all
    use ⟨‖x.1‖⁻¹ • x.1, by simp; rw [norm_smul]; field_simp⟩
    unfold lift_unit_circle; simp
    show mk ℝ (‖x.1‖⁻¹ • x.1) _ = mk ℝ x.1 _
    rw [mk_eq_mk_iff]
    use Units.mk ‖x.1‖⁻¹ ‖x.1‖ (by field_simp) (by field_simp)
    simp
  )

/-- List from unit circle to projectivization is continuous. -/
lemma continuous_lift_unit_circle {n:ℕ} : Continuous (@lift_unit_circle n) := by
  unfold lift_unit_circle
  refine Continuous.comp' ?hg ?hf;
  · exact { isOpen_preimage := fun s a ↦ a }
  exact Isometry.continuous fun x1 ↦ congrFun rfl

/-- Unit circle is compact. -/
instance {n:ℕ} : CompactSpace {v : Fin n → ℝ // dist v 0 = 1} := Metric.sphere.compactSpace 0 1

/-- Projectivization is compact. -/
instance {n:ℕ} : CompactSpace (ℙ ℝ (Fin n → ℝ)) := by
  let Q := IsCompact.image CompactSpace.isCompact_univ (@continuous_lift_unit_circle n)
  have : lift_unit_circle '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective (@surjective_lift_unit_circle n)
  exact {
      isCompact_univ := by rw [← this];exact Q
  }

/-- The real projective line ℙ ℝ (Fin 2 → ℝ) and OnePoint ℝ are homeomorphic.-/
noncomputable def onepointhomeo : Homeomorph (ℙ ℝ (Fin 2 → ℝ)) (OnePoint ℝ) :=
  @Continuous.homeoOfEquivCompactToT2 (ℙ ℝ (Fin 2 → ℝ)) (OnePoint ℝ) _ _ _ _ field_slope_equiv.symm
  div_slope_continuous
