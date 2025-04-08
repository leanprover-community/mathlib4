/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Topology.Compactification.OnePointEquiv
import Mathlib.Topology.Compactification.OnePointRealLemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.ProperSpace.Real
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



open Classical in
/-- OnePoint_div -/
noncomputable def OnePoint_div {K : Type} [DivisionRing K] (a : K) (r : K): OnePoint K :=
    ite (r ≠ 0) (a / r) ∞

/-- -/
infix:50 " ÷ " => OnePoint_div


/-- div_slope is well-defined. -/
lemma div_slope_well_defined {K : Type} [Field K]
    (a b : { v : Fin 2 → K // v ≠ 0 })
    (h : ∃ c : Kˣ, (fun m : Kˣ ↦ m • b.1) c = a.1) :
    (fun u ↦ u.1 0 ÷ u.1 1) a = (fun u ↦ u.1 0 ÷ u.1 1) b := by
  obtain ⟨c,hc⟩ := h
  simp_all only
  rw [← hc]; unfold OnePoint_div; simp only [ne_eq, Fin.isValue, Pi.smul_apply, ite_not]
  split_ifs with hbc hb hb
  · rfl
  · simp_all only [ne_eq, OnePoint.infty_ne_coe]
    apply hb;exact (Units.mul_right_eq_zero c).mp hbc
  · rw [hb] at hbc;simp at hbc
  · apply congrArg some
    field_simp
    show c * b.1 0 * b.1 1 = b.1 0 * (c * b.1 1)
    ring

/-- Function underlying homeomorphism. -/
noncomputable def div_slope (p : ℙ ℝ (Fin 2 → ℝ)) : OnePoint ℝ :=
  Quotient.lift
    (fun u : { v : Fin 2 → ℝ // v ≠ 0} ↦
      OnePoint_div (u.1 0) (u.1 1)) div_slope_well_defined p

/-- A pair is nonzero if the corresponding tuple is nonzero. -/
lemma nonzero_of_nonzero (a : {v : Fin 2 → ℝ // v ≠ 0}) :
    (a.1 0, a.1 1) ≠ 0 := by
  have := a.2
  contrapose this
  simp_all only [ne_eq, Prod.mk_eq_zero, not_and, Classical.not_imp, Decidable.not_not]
  ext z
  fin_cases z <;> simp_all


/-- Equivalence between two parametrizations of "lines through the origin". -/
noncomputable def tupFinNonzero :
  { p : ℝ × ℝ // p ≠ 0} ≃ {p : Fin 2 → ℝ // p ≠ 0} where
  toFun := by
    intro p
    exact ⟨![p.1.1, p.1.2], by
      have := p.2
      contrapose this
      simp_all only [ne_eq, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and,
        Classical.not_imp, Decidable.not_not]
      ext <;> simp_all
    ⟩
  invFun := by
    intro p
    exact ⟨(p.1 0,p.1 1),by
      have := p.2
      contrapose this
      simp_all only [ne_eq, Prod.mk_eq_zero, not_and, Classical.not_imp, Decidable.not_not]
      ext i
      simp_all only [Pi.zero_apply]
      fin_cases i <;> tauto
    ⟩
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp only [ne_eq, Fin.isValue]
    ext i
    simp_all only
    fin_cases i <;> tauto

/-- Equivalence between two forms of projective line. -/
noncomputable def projFinTup :
  ℙ ℝ (Fin 2 → ℝ) ≃ ℙ ℝ (ℝ × ℝ) where
  toFun := Quotient.lift
      (fun w : {p : Fin 2 → ℝ // p ≠ 0} => (Quotient.mk _ (tupFinNonzero.invFun w) : ℙ ℝ (ℝ × ℝ)))
      (fun u v huv => Quotient.sound <| by
        obtain ⟨c,hc⟩ := huv
        use c
        aesop)
  invFun := by
    let f : { p : ℝ × ℝ // p ≠ 0} → ℙ ℝ (Fin 2 → ℝ) :=
      fun w => Quotient.mk _ (tupFinNonzero.toFun w)
    refine Quotient.lift f (by
      intro a b hab; unfold f;
      refine Quotient.sound ?_
      obtain ⟨c,hc⟩ := hab
      use c
      unfold tupFinNonzero
      ext i
      fin_cases i <;>
      · simp only [ne_eq, Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero]
        rw [← hc]
        simp
    )
  left_inv := by
    apply Quotient.ind
    intro a
    simp
  right_inv := by
    apply Quotient.ind
    intro a
    simp

/-- Express div_slope in terms of OnePointEquiv. -/
theorem reconcile :
    div_slope = (OnePoint.equivProjectivization ℝ).invFun ∘ projFinTup.toFun := by
  ext p
  exact @Quotient.ind {v : Fin 2 → ℝ // v ≠ 0}
    (projectivizationSetoid ℝ (Fin 2 → ℝ))
    (fun p => div_slope p = (OnePoint.equivProjectivization ℝ).symm (projFinTup p))
    (by
      intro v
      unfold div_slope projFinTup OnePoint.equivProjectivization tupFinNonzero
      unfold OnePoint_div
      simp only [ne_eq, Fin.isValue, ite_not, Quotient.lift_mk, Equiv.invFun_as_coe,
        Equiv.coe_fn_symm_mk, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      split_ifs with g₀
      · simp_rw [g₀]
        rw [Projectivization.lift]
        aesop
      · rw [Projectivization.lift]
        simp_all only [ne_eq, Quotient.lift_mk, ite_false]
        ring_nf
    ) p

/-- Equivalence OnePoint ℝ ≃ ℙ ℝ (Fin 2 → ℝ). -/
noncomputable def div_slope_equiv :
  OnePoint ℝ ≃ ℙ ℝ (Fin 2 → ℝ) where
  toFun     := projFinTup.invFun ∘ (OnePoint.equivProjectivization ℝ).toFun
  invFun    := div_slope
  left_inv  := by
    rw [reconcile]
    show Function.LeftInverse (⇑(OnePoint.equivProjectivization ℝ).symm ∘ ⇑projFinTup)
      (⇑projFinTup.symm ∘ ⇑(OnePoint.equivProjectivization ℝ))
    intro
    simp
  right_inv := by
    rw [reconcile]
    show Function.RightInverse ((OnePoint.equivProjectivization ℝ).invFun ∘ projFinTup.toFun)
      (projFinTup.invFun ∘ (OnePoint.equivProjectivization ℝ).toFun)
    intro
    simp

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

/-- Auxiliary nhds lemma. -/
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

/-- Auxiliary uniformity lemma. -/
lemma slope_uniform_of_compact_pos {n : ℕ} {i j : Fin n}
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin n → ℝ // v ≠ 0 }}
    (H : a.1 j = 0)
    (hl : a.1 i > 0) : ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 j = 0 then ∞ else some (u.1 i / u.1 j)) ⁻¹' t :=  by
  have W := IsCompact.isBounded (ht₀)
  rw [Bornology.isBounded_def] at W
  simp only [Real.cobounded_eq, compl_compl, Filter.mem_sup, Filter.mem_atBot_sets,
    Set.mem_preimage, Filter.mem_atTop_sets, ge_iff_le] at W
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
    simp only [ne_eq] at h_x
    have hx : dist a x < δ := h_x
    clear h_x
    simp only [ne_eq, Fin.isValue, Set.mem_preimage]
    by_cases hz : x.1 j = 0
    · rw [hz];simp only [↓reduceIte];tauto
    · rw [if_neg hz]
      apply hamax
      by_cases hpos : x.1 j > 0
      · right
        have : dist a x = dist a.1 x.1 := rfl
        have hδ' := hδ.2 x.1 (by rw [dist_comm];linarith)
        tauto
      · left
        have h₁: x.1 j < 0 := lt_of_le_of_ne (le_of_not_lt hpos) hz
        rw [dist_comm] at hx
        have : dist x.1 a.1 < δ := hx
        have h₀: dist x.1 a.1 ≤ δ := by linarith
        exact (hδ.2 x h₀).1 h₁

/-- Auxiliary uniformity lemma. -/
lemma slope_uniform_of_compact_neg {n : ℕ} {i j : Fin n} {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ) (ht₂ : ∞ ∈ t)
    {a : { v : Fin n → ℝ // v ≠ 0 }} (H : a.1 j = 0) (hl : a.1 i < 0) :
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 j = 0 then ∞ else some (u.1 i / u.1 j)) ⁻¹' t :=  by
  have W := IsCompact.isBounded (ht₀)
  rw [Bornology.isBounded_def] at W
  simp only [Real.cobounded_eq, compl_compl, Filter.mem_sup, Filter.mem_atBot_sets,
    Set.mem_preimage, Filter.mem_atTop_sets, ge_iff_le] at W
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
    by_cases X : x.1 j = 0
    · rw [X];simp only [↓reduceIte];tauto
    · rw [if_neg X];
      apply hamax
      by_cases hpos : x.1 j > 0
      · left
        have : dist a x = dist a.1 x.1 := rfl
        have hδ' := hδ.2 x.1 (by rw [dist_comm];linarith)
        tauto
      · right
        have hneg: x.1 j < 0 := lt_of_le_of_ne (le_of_not_lt hpos) X
        rw [dist_comm] at hx
        have : dist x.1 a.1 < δ := hx
        have h₀: dist x.1 a.1 ≤ δ := by linarith
        exact (hδ.2 x h₀).2 hneg

/-- slopeUniform from compactness. -/
lemma slopeUniform_of_compact {n : ℕ} {j : Fin n}
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin n → ℝ // v ≠ 0 }}
    (H : a.1 j = 0) :
    ∃ i,
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 j = 0 then ∞ else some (u.1 i / u.1 j)) ⁻¹' t := by
  obtain ⟨i,hi⟩ := @posOrNeg n a
  use i
  cases hi with
  |inl hl => exact slope_uniform_of_compact_pos ht₀ ht₂ H hl
  |inr hr => exact slope_uniform_of_compact_neg ht₀ ht₂ H hr

/-- Auxiliary uniformity lemma requiring Fin 2. -/
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

/-- Auxiliary openness lemma. -/
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
  simp_all only [ne_eq, Set.mem_preimage, Filter.le_principal_iff]
  by_cases H : a.1 1 = 0
  · have Q := slope_uniform_of_compact ht₀ ht₂ H
    obtain ⟨V,hV⟩ := Q
    rw [nhds_eq_comap_uniformity]
    simp only [Fin.isValue, Filter.mem_comap]
    use V
    simp_all only [div_zero, ite_true, ne_eq,
      true_and];tauto
  · exact slope_open_nonzero ht₀ ht₁ ha H

/-- Auxiliary continuity lemma. -/
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

/-- Auxiliary continuity lemma. -/
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

lemma nonzero_of_dist_one {n : ℕ} (p : {v : Fin n → ℝ // dist v 0 = 1}) :
    p.1 ≠ 0 := by
      intro hc
      apply @one_ne_zero ℝ
      rw [← p.2, hc]
      exact dist_self 0

/-- List from unit circle to projectivization. -/
def liftUnitCircle {n:ℕ} (v : {v : Fin n → ℝ // dist v 0 = 1}) : ℙ ℝ (Fin n → ℝ) :=
    mk' ℝ ⟨v.1, nonzero_of_dist_one _⟩



/-- List from unit circle to projectivization is surjective. -/
lemma surjective_liftUnitCircle {n:ℕ} :
    Function.Surjective (@liftUnitCircle n) :=
  Quotient.ind (fun x ↦ by
    have := x.2
    have : ‖x.1‖ ≠ 0 := by simp_all
    use ⟨‖x.1‖⁻¹ • x.1, by simp only [ne_eq, dist_zero_right]; rw [norm_smul]; field_simp⟩
    unfold liftUnitCircle; simp only [ne_eq, mk'_eq_mk]
    show mk ℝ (‖x.1‖⁻¹ • x.1) _ = mk ℝ x.1 _
    rw [mk_eq_mk_iff]
    use Units.mk ‖x.1‖⁻¹ ‖x.1‖ (by field_simp) (by field_simp)
    simp
  )

instance {n : ℕ}: Setoid {v : Fin n → ℝ // v ≠ 0} :=
    projectivizationSetoid (K := ℝ) (V := (Fin n → ℝ))


/-- Lift from (part of) unit circle to projectivization is injective. -/
lemma injective_liftUnitCircle {n : ℕ} : Function.Injective
    (fun p :{ w : { v : Fin n.succ → ℝ // dist v 0 = 1 } // w.1 0 > 0}
        => @liftUnitCircle n.succ p.1) := by
  unfold Function.Injective
  intro p q h
  unfold liftUnitCircle at h
  simp at h
  have hQ := @Quotient.eq {v : Fin n.succ → ℝ // v ≠ 0}
    (@projectivizationSetoid ℝ (Fin n.succ → ℝ) _ _ _)
    ⟨p.1,nonzero_of_dist_one _⟩
    ⟨q.1,nonzero_of_dist_one _⟩
  have H := hQ.mp h
  obtain ⟨c,hc⟩ := H
  simp at hc
  have hp := p.1.2
  have hq := q.1.2
  apply Subtype.ext
  apply Subtype.ext
  rw [dist_pi_def] at hp hq
  simp at hp hq
  rw [← hc] at hp
  simp at hp
  have g₀ (b : Fin n.succ) := @nnnorm_smul ℝ ℝ _ _ _ _ c (q.1.1 b)
  have h₀ : (Finset.univ.sup fun b ↦  ‖c.1‖₊ * ‖q.1.1 b‖₊) = 1 := by
    rw [← hp]
    congr
    ext b
    exact Eq.symm ((fun {r₁ r₂} ↦ NNReal.coe_inj.mpr) (g₀ b))
  have h₁ : (Finset.univ.sup fun b ↦ ‖c.1‖₊ * ‖q.1.1 b‖₊)
    = ‖c.1‖₊ * (Finset.univ.sup fun b ↦  ‖q.1.1 b‖₊) := by
    exact Eq.symm (NNReal.mul_finset_sup ‖c.1‖₊ Finset.univ fun b ↦ ‖q.1.1 b‖₊);
  rw [h₁, hq] at h₀
  simp at h₀
  have g₁ : c = 1 := by
    refine Units.val_eq_one.mp ?_
    refine Real.toNNReal_eq_one.mp ?_
    rw [← h₀]
    refine Real.toNNReal_eq_nnnorm_of_nonneg ?hr
    have : c • q.1.1 0 = p.1.1 0 := by
        have c₀:= congrFun hc 0
        aesop
    -- have H : c = 1 ∨ c = -1 := by
    --     clear hQ hp hq g₀ h₁ hc this h p q
    --     sorry
    have : c.1 = 1 ∨ c.1 = -1 := by
        clear hQ hp hq g₀ h₁ hc this h p q
        have :  ‖c.1‖₊ = |c.1| := by exact rfl
        simp_all only [NNReal.coe_one]
        exact eq_or_eq_neg_of_abs_eq rfl
    cases this with
    | inl h =>
        simp_all
    | inr h =>
        exfalso
        rw [show c • q.1.1 0 = c.1 * q.1.1 0 by rfl] at this
        rw [h] at this
        simp at this
        have := p.2
        have := q.2
        linarith
  rw [g₁] at hc
  simp_all


/-- List from unit circle to projectivization is continuous. -/
lemma continuous_liftUnitCircle {n:ℕ} : Continuous (@liftUnitCircle n) := by
  unfold liftUnitCircle
  refine Continuous.comp' ?hg ?hf;
  · exact { isOpen_preimage := fun s a ↦ a }
  exact Isometry.continuous fun x1 ↦ congrFun rfl

/-- Unit circle is compact. -/
instance {n:ℕ} : CompactSpace {v : Fin n → ℝ // dist v 0 = 1} := Metric.sphere.compactSpace 0 1

instance {n:ℕ} : T2Space {v : Fin n → ℝ // dist v 0 = 1} := inferInstance

-- Create an equiv between unit circle and projectivization to show T2ness.

/-- Projectivization is compact. -/
instance {n:ℕ} : CompactSpace (ℙ ℝ (Fin n → ℝ)) := by
  let Q := IsCompact.image CompactSpace.isCompact_univ (@continuous_liftUnitCircle n)
  have : liftUnitCircle '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective (@surjective_liftUnitCircle n)
  exact {
      isCompact_univ := by rw [← this];exact Q
  }


/-- The real projective line ℙ ℝ (Fin 2 → ℝ) and OnePoint ℝ are homeomorphic. -/
noncomputable def OnePointHomeo : Homeomorph (ℙ ℝ (Fin 2 → ℝ)) (OnePoint ℝ) :=
  Continuous.homeoOfEquivCompactToT2 (f := div_slope_equiv.symm) div_slope_continuous

/-- The real projective line is a Hausdorff space. -/
instance :  T2Space (ℙ ℝ (Fin 2 → ℝ)) := Homeomorph.t2Space OnePointHomeo.symm

/-- Horizontal map has range missing one point. -/
theorem horizontal_hasRange :
    Set.range (fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ)))
                     = {⟦⟨![1, 0], by simp⟩⟧}ᶜ := Set.ext <| Quotient.ind <| fun p => by
  simp only [ne_eq, Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨y,hy⟩ hc
    have ⟨c,hc⟩ := Quotient.eq.mp <| Eq.trans hy hc
    simp only [Matrix.smul_cons, smul_zero, Matrix.smul_empty] at hc
    have : ![c • 1, 0] 1 = ![y, 1] 1 := congrFun hc 1
    simp_all
  · intro h
    rw [Quotient.eq] at h
    by_cases H₁ : p.1 1 = 0
    · exfalso
      apply h
      use ⟨p.1 0, 1 / p.1 0, by
          have := p.2
          contrapose this
          simp only [Decidable.not_not]
          ext i
          fin_cases i
          · contrapose this
            simp_all
          · exact H₁, by
          have : p.1 0 ≠ 0 := fun H₀ => p.2 <| funext <| fun i => by
              fin_cases i; exact H₀; exact H₁
          simp only [ne_eq, Fin.isValue, one_div]
          exact inv_mul_cancel₀ this
      ⟩
      ext i
      fin_cases i
      · simp
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ne_eq, Fin.isValue, one_div,
        Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.head_cons, smul_zero]
        tauto
    · use p.1 0 / p.1 1
      apply Quotient.sound
      use ⟨1 / p.1 1, p.1 1,by simp_all, by simp_all⟩
      ext i
      fin_cases i
      · simp only [ne_eq, Fin.isValue, one_div, Fin.zero_eta, Pi.smul_apply,
        Matrix.cons_val_zero, Units.smul_mk_apply, smul_eq_mul]
        ring_nf
      · simp only [ne_eq, Fin.isValue, one_div, Fin.mk_one, Pi.smul_apply,
        Units.smul_mk_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons]
        aesop

/-- Horizontal map is injective. -/
theorem horizontal_isInjective :
    Function.Injective fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ)) := by
  intro x y h
  obtain ⟨c,hc⟩ := Quotient.eq.mp h
  simp only [Matrix.smul_cons] at hc
  rw [show c • y = c.1 * y by rfl, show c • 1 = c.1 * 1 by rfl] at hc
  have := congrFun hc 1
  have := congrFun hc 0
  simp_all

lemma div_slope_equiv_open : IsOpenMap (fun r : ℝ => div_slope_equiv r) :=
    IsOpenMap.comp (fun S =>
    (show ⇑div_slope_equiv '' S = OnePointHomeo.toFun ⁻¹' S by aesop)
    ▸ OnePointHomeo.continuous_toFun.isOpen_preimage S) OnePoint.isOpenMap_coe

lemma horizontalContinuous : Continuous (fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ))) := by
    apply Continuous.comp' continuous_quotient_mk'
    apply Continuous.subtype_mk <| continuous_pi fun i => by
      fin_cases i
      · exact continuous_id'
      · exact continuous_const

/-- Horizontal map is inducing. -/
theorem horizontal_isInducing :
    Topology.IsInducing fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ)) :=
    Topology.isInducing_iff_nhds.mpr <| fun x => by
    ext s
    simp only [ne_eq, Filter.mem_comap]
    rw [mem_nhds_iff_exists_Ioo_subset ]
    simp_rw [mem_nhds_iff]
    constructor
    · intro h
      obtain ⟨l,u,hu⟩ := h
      let f := fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ))
      use f '' (Set.Ioo l u)
      constructor
      · exact ⟨f '' (Set.Ioo l u), fun _ => id,
          ⟨div_slope_equiv_open _ isOpen_Ioo, x, hu.1, rfl⟩⟩
      · exact fun a ha => hu.2 <| by
          obtain ⟨y,hy⟩ := ha
          have := hy.2
          simp only at this
          have : ![y, 1] = ![a, 1] := by
            rw [Quotient.eq] at hy
            obtain ⟨c,hc⟩ := hy.2
            simp only [Matrix.smul_cons] at hc
            rw [show c • a = c * a by rfl, show c • 1 = c.1 * 1 by rfl] at hc
            have := congrFun hc 0
            have := congrFun hc 1
            simp_all
          have : y = a := by
            have := congrFun this 0
            aesop
          aesop
    · intro h
      obtain ⟨t,ht⟩ := h
      obtain ⟨t₁,ht₁⟩ := ht.1
      have h₁ : IsOpen <|(fun r ↦ ⟦⟨![r, 1], by simp⟩⟧) ⁻¹' t₁ :=
          horizontalContinuous.isOpen_preimage t₁ ht₁.2.1
      rw [← mem_nhds_iff_exists_Ioo_subset]
      exact Filter.mem_of_superset (IsOpen.mem_nhds h₁ (by aesop))
        fun _ hz => ht.2 <| ht₁.1 hz

/-- Uniqueness-based proof that
  the real projective line ℙ ℝ (Fin 2 → ℝ) and OnePoint ℝ are homeomorphic. -/
noncomputable def OnePointReal_homeo_proj_Katz : Homeomorph (OnePoint ℝ) (ℙ ℝ (Fin 2 → ℝ)) :=
  OnePoint.equivOfIsEmbeddingOfRangeEq (Y := ℙ ℝ (Fin 2 → ℝ))
  ⟦ ⟨![1,0],by simp⟩ ⟧ (fun r => ⟦ ⟨![r,1],by simp⟩ ⟧)
  ⟨horizontal_isInducing, horizontal_isInjective⟩ horizontal_hasRange
