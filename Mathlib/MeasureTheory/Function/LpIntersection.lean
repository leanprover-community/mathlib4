/-
Copyright (c) 2025 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter
open scoped ENNReal

/-! # Intersection of multiple `L^p` spaces -/

section Intersection

-- @[to_additive]
-- def Subsemigroup.inf_fst {M : Type*} [Monoid M] {s t : Subsemigroup M} : ↑(s ⊓ t) →ₙ* s where
--   toFun x := ⟨x.1, x.2.1⟩
--   map_mul' _ _ := rfl

-- @[to_additive]
-- def Subsemigroup.inf_snd {M : Type*} [Monoid M] {s t : Subsemigroup M} : ↑(s ⊓ t) →ₙ* t where
--   toFun x := ⟨x.1, x.2.2⟩
--   map_mul' _ _ := rfl

-- @[to_additive]
-- def Submonoid.inf_fst {M : Type*} [Monoid M] {s t : Submonoid M} : ↑(s ⊓ t) →* s :=
--   { Subsemigroup.inf_fst with map_one' := rfl }

-- @[to_additive]
-- def Submonoid.inf_snd {M : Type*} [Monoid M] {s t : Submonoid M} : ↑(s ⊓ t) →* t :=
--   { Subsemigroup.inf_snd with map_one' := rfl }

section Subgroup

variable {G : Type*} [Group G] {s t : Subgroup G}

@[to_additive]
def Subgroup.inf_fst : ↑(s ⊓ t) →* s :=
  -- Submonoid.inf_fst
  { toFun x := ⟨x.1, x.2.1⟩, map_one' := rfl, map_mul' _ _ := rfl }

@[to_additive]
def Subgroup.inf_snd : ↑(s ⊓ t) →* t :=
  -- Submonoid.inf_snd
  { toFun x := ⟨x.1, x.2.2⟩, map_one' := rfl, map_mul' _ _ := rfl }

@[to_additive (attr := simp)]
def Subgroup.inf_fst_val (x : ↑(s ⊓ t)) : (inf_fst x).val = x.val := rfl

@[to_additive (attr := simp)]
def Subgroup.inf_snd_val (x : ↑(s ⊓ t)) : (inf_snd x).val = x.val := rfl

@[to_additive (attr := simp)]
theorem Subgroup.inf_fst_eq_one_iff (x : ↑(s ⊓ t)) : inf_fst x = 1 ↔ x = 1 := by
  simp only [Subtype.ext_iff_val]
  simp

@[to_additive (attr := simp)]
theorem Subgroup.inf_snd_eq_one_iff (x : ↑(s ⊓ t)) : inf_snd x = 1 ↔ x = 1 := by
  simp only [Subtype.ext_iff_val]
  simp

end Subgroup

end Intersection


section LpInf

namespace MeasureTheory

variable {𝕜 α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedField 𝕜] [NormedSpace 𝕜 E] {p q : ℝ≥0∞} {p₁ p₂ q₁ q₁ : ℝ≥0∞} {μ : Measure α}

noncomputable instance Lp.instInfCoeFun : CoeFun ↑(Lp E p μ ⊓ Lp E q μ) (fun _ ↦ α → E) where
  coe f := f

instance Lp.instInfModule : Module 𝕜 ↑(Lp E p μ ⊓ Lp E q μ) :=
  (Lp.LpSubmodule E p μ 𝕜 ⊓ Lp.LpSubmodule E q μ 𝕜).module

theorem Lp.coeFn_smul_inf (c : 𝕜) (f : ↑(Lp E p μ ⊓ Lp E q μ)) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  AEEqFun.coeFn_smul c f.1

variable (E p₁ p₂ μ) in
noncomputable def Lp.norm_inf_fst [Fact (1 ≤ p₁)] :
    AddGroupNorm ↑(Lp E p₁ μ ⊓ Lp E p₂ μ) :=
  { toFun f := ‖AddSubgroup.inf_fst f‖
    map_zero' := by simp
    add_le' f g := norm_add_le (AddSubgroup.inf_fst f) (AddSubgroup.inf_fst g)
    neg' f := by simp
    eq_zero_of_map_eq_zero' f := by simp }

variable (E p₁ p₂ μ) in
noncomputable def Lp.norm_inf_snd [Fact (1 ≤ p₂)] :
    AddGroupNorm ↑(Lp E p₁ μ ⊓ Lp E p₂ μ) :=
  { toFun f := ‖AddSubgroup.inf_snd f‖
    map_zero' := by simp
    add_le' f g := norm_add_le (AddSubgroup.inf_snd f) (AddSubgroup.inf_snd g)
    neg' f := by simp
    eq_zero_of_map_eq_zero' f := by simp }

@[simp] theorem Lp.norm_inf_fst_apply [Fact (1 ≤ p₁)] (f : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ)) :
    norm_inf_fst E p₁ p₂ μ f = ‖AddSubgroup.inf_fst f‖ := rfl

@[simp] theorem Lp.norm_inf_snd_apply [Fact (1 ≤ p₂)] (f : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ)) :
    norm_inf_snd E p₁ p₂ μ f = ‖AddSubgroup.inf_snd f‖ := rfl

-- TODO: Move
@[simp] theorem _root_.Real.toNNReal_max (r p : ℝ) :
    Real.toNNReal (r ⊔ p) = (Real.toNNReal r) ⊔ (Real.toNNReal p) := by
  cases le_or_lt r p with
  | inl h => simpa [h] using Real.toNNReal_le_toNNReal h
  | inr h => simpa [h.le] using Real.toNNReal_le_toNNReal h.le

-- TODO: Move
@[simp] theorem _root_.ENNReal.ofReal_max (r p : ℝ) :
    ENNReal.ofReal (r ⊔ p) = (ENNReal.ofReal r) ⊔ (ENNReal.ofReal p) := by
  simp [ENNReal.ofReal]

-- Need this for CompleteSpace (gives UniformSpace).
noncomputable instance Lp.instInfNormedAddCommGroup [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] :
    NormedAddCommGroup ↑(Lp E p₁ μ ⊓ Lp E p₂ μ) :=
  { (Lp.norm_inf_fst E p₁ p₂ μ ⊔ Lp.norm_inf_snd E p₁ p₂ μ).toNormedAddCommGroup with
    edist f g :=
      edist (AddSubgroup.inf_fst f) (AddSubgroup.inf_fst g) ⊔
      edist (AddSubgroup.inf_snd f) (AddSubgroup.inf_snd g)
    edist_dist f g := by
      -- simp [dist, Lp.edist_dist]  -- Works but slow?
      simp only [dist, AddGroupNorm.toAddGroupSeminorm_eq_coe, AddGroupNorm.sup_apply,
        norm_inf_fst_apply, norm_inf_snd_apply, map_sub, Lp.edist_dist, ENNReal.ofReal_max]
  }

theorem Lp.norm_inf_def [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (f : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ)) :
    ‖f‖ = ‖AddSubgroup.inf_fst f‖ ⊔ ‖AddSubgroup.inf_snd f‖ := rfl

theorem Lp.dist_inf_def [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (f g : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ)) :
    dist f g = (dist (AddSubgroup.inf_fst f) (AddSubgroup.inf_fst g) ⊔
      dist (AddSubgroup.inf_snd f) (AddSubgroup.inf_snd g)) := rfl

theorem Lp.edist_inf_def [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (f g : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ)) :
    edist f g = (edist (AddSubgroup.inf_fst f) (AddSubgroup.inf_fst g) ⊔
      edist (AddSubgroup.inf_snd f) (AddSubgroup.inf_snd g)) := rfl

theorem Lp.uniformContinuous_inf_fst [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] :
    UniformContinuous (AddSubgroup.inf_fst : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ) → _) :=
  AddMonoidHomClass.uniformContinuous_of_bound _ 1 fun _ ↦ by
    simpa only [one_mul, Lp.norm_inf_def] using le_sup_left

theorem Lp.uniformContinuous_inf_snd [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] :
    UniformContinuous (AddSubgroup.inf_snd : ↑(Lp E p₁ μ ⊓ Lp E p₂ μ) → _) :=
  AddMonoidHomClass.uniformContinuous_of_bound _ 1 fun _ ↦ by
    simpa only [one_mul, Lp.norm_inf_def] using le_sup_right

theorem Lp.mk_mem_inf_of_eLpNorm_lt_top (f : α → E) (hf_meas : AEStronglyMeasurable f μ)
    (hf_fst : eLpNorm f p₁ μ < ⊤) (hf_snd : eLpNorm f p₂ μ < ⊤) :
    AEEqFun.mk f hf_meas ∈ Lp E p₁ μ ⊓ Lp E p₂ μ := by
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mem_Lp_iff_eLpNorm_lt_top.mpr <| eLpNorm_aeeqFun hf_meas ▸ hf_fst
  · exact mem_Lp_iff_eLpNorm_lt_top.mpr <| eLpNorm_aeeqFun hf_meas ▸ hf_snd

theorem Lp.mk_mem_inf_of_memℒp (f : α → E) (hf_fst : Memℒp f p₁ μ) (hf_snd : Memℒp f p₂ μ) :
    AEEqFun.mk f hf_fst.1 ∈ Lp E p₁ μ ⊓ Lp E p₂ μ :=
  Lp.mk_mem_inf_of_eLpNorm_lt_top f hf_fst.1 hf_fst.2 hf_snd.2

-- TODO: Useful to generalize to `[SemilatticeSup ι] [IsDirected ι fun (x1 x2 : ι) ↦ x1 ≤ x2]`?
/-- If a sequence converges in measure to two different functions, then the measure of the set
on which they differ by at least `r` is zero for any `r > 0`. -/
theorem tendstoInMeasure_measure_dist_ge_eq_zero {fs : ℕ → α → E} {f g : α → E}
    (hf : TendstoInMeasure μ fs atTop f) (hg : TendstoInMeasure μ fs atTop g) :
    ∀ r > 0, μ {x | r ≤ ‖f x - g x‖} = 0 := by
  intro r hr
  suffices μ {x | r ≤ ‖f x - g x‖} ≤ 0 by simpa
  refine le_of_forall_lt' fun ε hε ↦ ?_
  replace hε : 0 < (1 ⊓ ε) / 3 := ENNReal.div_pos (ne_of_gt <| by simp [hε]) (by simp)
  -- Bound above by `(1 − ε) / 3` to obtain strict inequality and handle `ε = ⊤`.
  simp only [tendstoInMeasure_iff_norm, ENNReal.tendsto_nhds_zero, eventually_atTop] at hf hg
  rcases hf (r / 2) (half_pos hr) ((1 ⊓ ε) / 3) hε with ⟨N₁, hN₁⟩
  rcases hg (r / 2) (half_pos hr) ((1 ⊓ ε) / 3) hε with ⟨N₂, hN₂⟩
  calc μ {x | r ≤ ‖f x - g x‖}
  _ ≤ μ ({x | r / 2 ≤ ‖f x - fs (N₁ ⊔ N₂) x‖} ∪ {x | r / 2 ≤ ‖fs (N₁ ⊔ N₂) x - g x‖}) := by
    refine measure_mono ?_
    refine Set.setOf_subset.mpr fun x hx ↦ ?_
    simp only [Set.mem_union, Set.mem_setOf_eq]
    refine le_or_le_of_add_le_add ?_
    simp only [add_halves]
    exact le_trans hx (norm_sub_le_norm_sub_add_norm_sub _ _ _)
  _ ≤ μ {x | r / 2 ≤ ‖f x - fs (N₁ ⊔ N₂) x‖} + μ {x | r / 2 ≤ ‖fs (N₁ ⊔ N₂) x - g x‖} :=
    measure_union_le _ _
  _ = μ {x | r / 2 ≤ ‖fs (N₁ ⊔ N₂) x - f x‖} + μ {x | r / 2 ≤ ‖fs (N₁ ⊔ N₂) x - g x‖} := by
    simp_rw [norm_sub_rev (f _)]
  _ ≤ (1 ⊓ ε) / 3 + (1 ⊓ ε) / 3 :=
    add_le_add (hN₁ (N₁ ⊔ N₂) le_sup_left) (hN₂ (N₁ ⊔ N₂) le_sup_right)
  _ < (1 ⊓ ε) / 3 + (1 ⊓ ε) / 3 + (1 ⊓ ε) / 3 := by
    refine ENNReal.lt_add_right ?_ ?_
    · refine ne_of_lt (ENNReal.add_lt_top.mpr ?_)
      rw [and_self]
      refine ENNReal.div_lt_top ?_ ?_ <;> simp
    · exact hε.ne'
  _ = (1 ⊓ ε) := ENNReal.add_thirds _
  _ ≤ ε := inf_le_right

-- TODO: Generalize from `ℕ` to `ι`?
/-- If a sequence converges in measure to two different functions, then they are ae-equal. -/
theorem tendstoInMeasure_unique {fs : ℕ → α → E} {f g : α → E}
    (hf : TendstoInMeasure μ fs atTop f) (hg : TendstoInMeasure μ fs atTop g) :
    f =ᵐ[μ] g := by
  suffices μ {x | f x ≠ g x} ≤ 0 by simpa
  calc μ {x | f x ≠ g x}
  _ ≤ μ (⋃ k : ℕ, {x | (k + 1 : ℝ)⁻¹ ≤ ‖f x - g x‖}) := by
    gcongr
    refine Set.setOf_subset.mpr fun x hx ↦ ?_
    simp only [Set.mem_iUnion]
    use ⌈‖f x - g x‖⁻¹⌉₊
    refine inv_le_of_inv_le₀ (norm_sub_pos_iff.mpr hx) ?_
    exact le_trans (Nat.le_ceil _) (lt_add_one _).le
  _ = 0 := by
    refine measure_iUnion_null fun k ↦ ?_
    exact tendstoInMeasure_measure_dist_ge_eq_zero hf hg (k + 1)⁻¹ Nat.inv_pos_of_nat

instance Lp.instInfCompleteSpace [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [CompleteSpace E] :
    CompleteSpace ↑(Lp E p₁ μ ⊓ Lp E p₂ μ) := by
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro fs hfs
  have hf : CauchySeq (AddSubgroup.inf_fst ∘ fs) := by simpa using hfs.map uniformContinuous_inf_fst
  have hg : CauchySeq (AddSubgroup.inf_snd ∘ fs) := by simpa using hfs.map uniformContinuous_inf_snd
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hf
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hg
  have hfg : f.1 = g.1 := AEEqFun.ext <| tendstoInMeasure_unique
    (by simpa using tendstoInMeasure_of_tendsto_Lp hf)
    (by simpa using tendstoInMeasure_of_tendsto_Lp hg)
  use ⟨f.1, ⟨f.2, hfg ▸ g.2⟩⟩
  rw [Metric.tendsto_atTop] at hf hg ⊢
  intro ε hε
  rcases hf ε hε with ⟨N, hN⟩
  rcases hg ε hε with ⟨M, hM⟩
  use N ⊔ M
  intro n hn
  calc dist (fs n) ⟨f, _⟩
  _ = dist (AddSubgroup.inf_fst (fs n)) f ⊔ dist (AddSubgroup.inf_snd (fs n)) g := by
    rw [dist_inf_def]
    congr
    exact SetLike.coe_eq_coe.mp hfg
  _ < ε := sup_lt_iff.mpr ⟨hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)⟩

end MeasureTheory

end LpInf
